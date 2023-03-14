use std::{
  collections::BTreeSet,
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
  str,
};

use nom::{
  branch::alt,
  character::complete::{alpha1, char, digit1, none_of},
  combinator::{all_consuming, map, map_opt, map_res, opt, value},
  multi::{fold_many0, fold_many1, separated_list0},
  sequence::{delimited, pair, preceded, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use super::{
  tokens::{meta, parenthesized, token},
  Expr, LitString, Type,
};
use crate::{CodegenContext, LocalContext, ParseContext};

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
enum RegConstraint {
  Reg,
  RegAbcd,
  RegByte,
  Freg,
}

impl ToTokens for RegConstraint {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Reg => quote! { reg },
      Self::RegAbcd => quote! { reg_abcd },
      Self::RegByte => quote! { reg_byte },
      Self::Freg => quote! { freg },
    })
  }
}

/// An inline assembly call.
///
/// ```c
/// #define ASM(src, dst) __asm__ (\
///     "mov %1, %0\n" \
///     "add $1, %0" \
///     : "=r" (dst) \
///     : "r" (src) \
///   );
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Asm {
  template: Vec<String>,
  outputs: Vec<(Dir, RegConstraint, Expr)>,
  inputs: Vec<(RegConstraint, Expr)>,
  clobbers: Vec<String>,
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
          // Escape Rust format string.
          map(alt((char('{'), char('}'))), |c| format!("{0}{0}", c)),
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
        s.split('\n')
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

  fn parse_reg_constraint(bytes: &[u8]) -> IResult<&[u8], RegConstraint> {
    map_opt(alpha1, |s: &[u8]| {
      if s.contains(&b'r') {
        Some(RegConstraint::Reg)
      } else if s.contains(&b'Q') {
        Some(RegConstraint::RegAbcd)
      } else if s.contains(&b'q') {
        Some(RegConstraint::RegByte)
      } else if s.contains(&b'f') {
        Some(RegConstraint::Freg)
      } else if s.contains(&b'i') || s.contains(&b'g') {
        Some(RegConstraint::Reg)
      } else {
        None
      }
    })(bytes)
  }

  fn parse_output_operands(bytes: &[u8]) -> IResult<&[u8], (Dir, RegConstraint)> {
    all_consuming(pair(alt((value(Dir::Out, char('=')), value(Dir::InOut, char('+')))), Self::parse_reg_constraint))(
      bytes,
    )
  }

  fn parse_input_operands(bytes: &[u8]) -> IResult<&[u8], RegConstraint> {
    all_consuming(Self::parse_reg_constraint)(bytes)
  }

  pub(crate) fn parse<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
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
              parenthesized(|tokens| Expr::parse(tokens, ctx)),
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
            parenthesized(|tokens| Expr::parse(tokens, ctx)),
          ),
        ),
      )),
      opt(preceded(
        delimited(meta, token(":"), meta),
        separated_list0(tuple((meta, token(","), meta)), map_res(LitString::parse, |s| String::from_utf8(s.repr))),
      )),
    )))(tokens)?;

    let outputs = outputs.unwrap_or_default();
    let inputs = inputs.unwrap_or_default();
    let clobbers = clobbers.unwrap_or_default();

    Ok((tokens, Self { template, outputs, inputs, clobbers }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    for (_, _, output) in self.outputs.iter_mut() {
      output.finish(ctx)?;
    }

    for (_, input) in self.inputs.iter_mut() {
      input.finish(ctx)?;
    }

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

    let mut clobbers: BTreeSet<_> = self.clobbers.iter().cloned().collect();

    let mut options = Vec::new();

    // Memory is not clobbered, so add `nomem` option.
    if !clobbers.remove("memory") {
      options.push(quote! { nomem });
    }

    // Flags are not clobbered, so add `preserves_flags` option.
    if !clobbers.remove("cc") {
      options.push(quote! { preserves_flags });
    }

    let options = if options.is_empty() { None } else { Some(quote! { options(#(#options),*), }) };

    let trait_prefix = ctx.trait_prefix();

    tokens.append_all(quote! {
      #trait_prefix arch::asm!(
        #(#template,)*
        #(#outputs,)*
        #(#inputs,)*
        #(out(#clobbers) _,)*
        clobber_abi("C"),
        #options
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
