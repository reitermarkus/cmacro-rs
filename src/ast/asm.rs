use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
  str,
};

use nom::{
  branch::alt,
  character::complete::{char, digit1, none_of},
  combinator::{all_consuming, map, map_opt, map_res, opt, value},
  complete::tag,
  multi::{fold_many0, fold_many1, many0, separated_list0},
  sequence::{delimited, pair, preceded, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use super::{
  tokens::{meta, parenthesized, token},
  Expr, Identifier, Lit, LitString, Type,
};
use crate::{CodegenContext, LocalContext};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dir {
  Out,
  InOut,
}

impl ToTokens for Dir {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Out => quote! { out },
      Self::InOut => quote! { inout },
    })
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reg {
  Reg,
  RegAbcd,
  RegByte,
  Freg,
}

impl ToTokens for Reg {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Reg => quote! { reg },
      Self::RegAbcd => quote! { reg_abcd },
      Self::RegByte => quote! { reg_byte },
      Self::Freg => quote! { freg },
    })
  }
}

/// An inline assemble call.
#[derive(Debug, Clone, PartialEq)]
pub struct Asm {
  template: Vec<String>,
  outputs: Vec<(Dir, Reg, Identifier)>,
  inputs: Vec<(Reg, Identifier)>,
  clobbers: Vec<Expr>,
}

impl Asm {
  fn parse_template(bytes: &[u8]) -> IResult<&[u8], Vec<String>> {
    all_consuming(map(
      fold_many0(
        alt((
          map(
            preceded(
              char('%'),
              map_opt(digit1, |s: &[u8]| {
                let s = str::from_utf8(s).ok()?;
                let n = s.parse::<usize>().ok()?;
                Some(n)
              }),
            ),
            |n| format!("{{{}}}", n),
          ),
          fold_many1(none_of::<_, _, nom::error::Error<&[u8]>>("%"), String::new, |mut acc, c| {
            acc.push(c);
            acc
          }),
        )),
        String::new,
        |mut acc, s| {
          acc.push_str(&s);
          acc
        },
      ),
      |s| {
        s.split("\n")
          .filter_map(|s| {
            let s = s.trim();
            if s.is_empty() {
              None
            } else {
              Some(s.to_owned())
            }
          })
          .collect()
      },
    ))(bytes)
  }

  fn parse_reg_constraint(bytes: &[u8]) -> IResult<&[u8], Reg> {
    alt((
      value(Reg::Reg, char('r')),
      value(Reg::RegAbcd, char('Q')),
      value(Reg::RegByte, char('q')),
      value(Reg::Freg, char('f')),
    ))(bytes)
  }

  fn parse_output_operands(bytes: &[u8]) -> IResult<&[u8], (Dir, Reg)> {
    all_consuming(pair(alt((value(Dir::Out, char('=')), value(Dir::InOut, char('+')))), Self::parse_reg_constraint))(
      bytes,
    )
  }

  fn parse_input_operands(bytes: &[u8]) -> IResult<&[u8], Reg> {
    all_consuming(Self::parse_reg_constraint)(bytes)
  }

  pub(crate) fn parse<I, C>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, (template, outputs, inputs, clobbers)) = parenthesized(tuple((
      delimited(
        meta,
        map_opt(LitString::parse, |s| {
          let (_, template) = Self::parse_template(s.as_bytes()).ok()?;
          Some(template)
        }),
        meta,
      ),
      opt(preceded(
        delimited(meta, token(":"), meta),
        separated_list0(
          delimited(meta, token(","), meta),
          map(
            pair(
              map_opt(LitString::parse, |s| {
                let (_, operands) = Self::parse_output_operands(s.as_bytes()).ok()?;
                Some(operands)
              }),
              parenthesized(Identifier::parse),
            ),
            |((dir, reg), id)| (dir, reg, id),
          ),
        ),
      )),
      opt(preceded(
        delimited(meta, token(":"), meta),
        separated_list0(
          delimited(meta, token(","), meta),
          pair(
            map_opt(LitString::parse, |s| {
              let (_, operands) = Self::parse_input_operands(s.as_bytes()).ok()?;
              Some(operands)
            }),
            parenthesized(Identifier::parse),
          ),
        ),
      )),
      opt(preceded(delimited(meta, token(":"), meta), separated_list0(tuple((meta, token(","), meta)), Expr::parse))),
    )))(tokens)?;

    let outputs = outputs.unwrap_or_default();
    let inputs = inputs.unwrap_or_default();

    let clobbers = clobbers
      .unwrap_or_default()
      .into_iter()
      .filter_map(|c| match c {
        Expr::Literal(Lit::String(s)) if s == "memory" => None,
        clobber => Some(clobber),
      })
      .collect::<Vec<_>>();

    Ok((tokens, Self { template, outputs, inputs, clobbers }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let template = &self.template;
    let outputs = self
      .outputs
      .iter()
      .map(|(dir, reg, var)| {
        let var = var.to_token_stream(ctx);
        quote! { #dir(#reg) #var }
      })
      .collect::<Vec<_>>();
    let inputs = self
      .inputs
      .iter()
      .map(|(reg, var)| {
        let var = var.to_token_stream(ctx);
        quote! { in(#reg) #var }
      })
      .collect::<Vec<_>>();
    let clobbers = self.clobbers.iter().map(|c| c.to_token_stream(ctx)).collect::<Vec<_>>();

    tokens.append_all(quote! {
      ::core::arch::asm!(
        #(#template,)*
        #(#outputs,)*
        #(#inputs,)*
        #(out(#clobbers) _,)*
        clobber_abi("C"),
      )
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_template() {
    let template = "btsl %2,%1\n\tsbb %0,%0".as_bytes();
    let (rest, template_tokens) = Asm::parse_template(template).unwrap();

    assert!(rest.is_empty());
    assert_eq!(template_tokens, vec!["btsl {2},{1}", "sbb {0},{0}"]);
  }
}
