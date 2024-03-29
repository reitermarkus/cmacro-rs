use std::{collections::BTreeSet, fmt::Debug, str};

use nom::{
  branch::alt,
  character::complete::{alpha1, char, digit1, none_of},
  combinator::{all_consuming, map, map_opt, opt, value},
  multi::{fold_many0, fold_many1, separated_list0},
  sequence::{delimited, pair, preceded, terminated, tuple},
  IResult,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use super::{
  tokens::{id, meta, parenthesized, punct},
  Expr, LitString, Type,
};
use crate::{CodegenContext, LocalContext, MacroToken};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Dir {
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
pub(crate) enum RegConstraint {
  Reg,
  RegAbcd,
  RegByte,
  Freg,
  Digit(u8),
}

impl ToTokens for RegConstraint {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Reg => quote! { reg },
      Self::RegAbcd => quote! { reg_abcd },
      Self::RegByte => quote! { reg_byte },
      Self::Freg => quote! { freg },
      Self::Digit(digit) => {
        let digit = proc_macro2::Literal::u8_unsuffixed(*digit);
        quote! { #digit }
      },
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Asm<'t> {
  pub(crate) template: Vec<String>,
  pub(crate) outputs: Vec<(Dir, RegConstraint, Expr<'t>)>,
  pub(crate) inputs: Vec<(RegConstraint, Expr<'t>)>,
  pub(crate) clobbers: Vec<String>,
}

impl<'t> Asm<'t> {
  fn parse_template(input: &str) -> IResult<&str, Vec<String>> {
    all_consuming(map(
      fold_many0(
        alt((
          preceded(
            char('%'),
            alt((
              map_opt(digit1, |s: &str| {
                let n = s.parse::<usize>().ok()?;
                Some(format!("{{{}}}", n))
              }),
              map(alpha1, |reg| format!("%{reg}")),
            )),
          ),
          // Escape Rust format string.
          map(alt((char('{'), char('}'))), |c| format!("{0}{0}", c)),
          fold_many1(none_of::<_, _, nom::error::Error<&str>>("%"), String::new, |mut acc, c| {
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
      |s| s.split('\n').map(|s| s.trim().to_owned()).collect(),
    ))(input)
  }

  fn parse_reg_constraint(input: &str) -> IResult<&str, RegConstraint> {
    alt((
      map_opt(alpha1, |s: &str| {
        if s.contains('r') {
          Some(RegConstraint::Reg)
        } else if s.contains('Q') {
          Some(RegConstraint::RegAbcd)
        } else if s.contains('q') {
          Some(RegConstraint::RegByte)
        } else if s.contains('f') {
          Some(RegConstraint::Freg)
        } else if s.contains('i') || s.contains('g') {
          Some(RegConstraint::Reg)
        } else if let Ok(digit) = s.parse::<u8>() {
          Some(RegConstraint::Digit(digit))
        } else {
          None
        }
      }),
      map_opt(digit1, |s: &str| if let Ok(digit) = s.parse::<u8>() { Some(RegConstraint::Digit(digit)) } else { None }),
    ))(input)
  }

  fn parse_output_operands(input: &str) -> IResult<&str, (Dir, RegConstraint)> {
    all_consuming(pair(alt((value(Dir::Out, char('=')), value(Dir::InOut, char('+')))), Self::parse_reg_constraint))(
      input,
    )
  }

  fn parse_input_operands(input: &str) -> IResult<&str, RegConstraint> {
    all_consuming(Self::parse_reg_constraint)(input)
  }

  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, (template, outputs, inputs, clobbers)) = preceded(
      terminated(alt((id("__asm__"), id("__asm"), id("asm"))), opt(alt((id("volatile"), id("inline"), id("goto"))))),
      parenthesized(tuple((
        delimited(
          meta,
          map_opt(LitString::parse, |s| {
            let (_, template) = Self::parse_template(s.as_str()?).ok()?;
            Some(template)
          }),
          meta,
        ),
        opt(preceded(
          delimited(meta, punct(":"), meta),
          separated_list0(
            delimited(meta, punct(","), meta),
            map(
              pair(
                map_opt(LitString::parse, |s| {
                  let (_, operands) = Self::parse_output_operands(s.as_str()?).ok()?;
                  Some(operands)
                }),
                parenthesized(Expr::parse),
              ),
              |((dir, reg), id)| (dir, reg, id),
            ),
          ),
        )),
        opt(preceded(
          delimited(meta, punct(":"), meta),
          separated_list0(
            delimited(meta, punct(","), meta),
            pair(
              map_opt(LitString::parse, |s| {
                let (_, operands) = Self::parse_input_operands(s.as_str()?).ok()?;
                Some(operands)
              }),
              parenthesized(Expr::parse),
            ),
          ),
        )),
        opt(preceded(
          delimited(meta, punct(":"), meta),
          separated_list0(tuple((meta, punct(","), meta)), map_opt(LitString::parse, |s| Some(s.as_str()?.to_owned()))),
        )),
      ))),
    )(tokens)?;

    let outputs = outputs.unwrap_or_default();
    let inputs = inputs.unwrap_or_default();
    let clobbers = clobbers.unwrap_or_default();

    Ok((tokens, Self { template, outputs, inputs, clobbers }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    for (_, _, output) in self.outputs.iter_mut() {
      output.finish(ctx)?;
    }

    for (_, input) in self.inputs.iter_mut() {
      input.finish(ctx)?;
    }

    if self.is_global() {
      ctx.export_as_macro = true;
    }

    Ok(None)
  }

  fn is_att_syntax(&self) -> bool {
    self.template.iter().any(|s| {
      // GCC template variables (e.g. `%0`) have already been replaced (e.g. `{{0}}`).
      // AT&T syntax uses e.g. `(%0,...)` while Intel syntax uses e.g. `[%0,...]` for
      // indirect addresses.
      s.contains("({") ||
      // Remaining `%` mean registers use AT&T syntax (e.g. `%eax`).
      s.contains('%') ||
      // Immediate values are prefixed with `$`.
      s.contains('$')
    })
  }

  fn is_global(&self) -> bool {
    self
      .template
      .iter()
      .any(|line| line.starts_with(".globl") || line.starts_with(".global") || line.starts_with(".section"))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let template = &self.template;

    let mut outputs = self.outputs.clone();
    let mut inputs = self.inputs.clone();

    for (constraint, _) in self.inputs.iter() {
      if let RegConstraint::Digit(d) = constraint {
        if let Some((ref mut dir, _, _)) = outputs.get_mut(*d as usize) {
          inputs.remove(*d as usize);
          *dir = Dir::InOut;
        }
      }
    }

    let outputs = outputs
      .iter()
      .map(|(dir, reg, var)| {
        let var = var.to_token_stream(ctx);
        quote! { #dir(#reg) #var }
      })
      .collect::<Vec<_>>();
    let inputs = inputs
      .iter()
      .map(|(reg, var)| {
        let var = var.to_token_stream(ctx);
        quote! { in(#reg) #var }
      })
      .collect::<Vec<_>>();

    let mut clobbers: BTreeSet<_> = self.clobbers.iter().cloned().collect();

    let mut options = Vec::new();

    if self.is_att_syntax() {
      options.push(quote! { att_syntax });
    }

    let (asm, clobber_abi) = if self.is_global() {
      (quote! { global_asm! }, None)
    } else {
      // Memory is not clobbered, so add `nomem` option.
      if !clobbers.remove("memory") {
        options.push(quote! { nomem });
      }

      // Flags are not clobbered, so add `preserves_flags` option.
      if !clobbers.remove("cc") {
        options.push(quote! { preserves_flags });
      }

      let clobber_abi = if clobbers.is_empty() { None } else { Some(quote! { clobber_abi("C"), }) };

      (quote! { asm! }, clobber_abi)
    };

    let options = if options.is_empty() { None } else { Some(quote! { options(#(#options),*), }) };

    let trait_prefix = ctx.trait_prefix().into_iter();
    tokens.append_all(quote! {
      #(#trait_prefix::)*arch::#asm(
        #(#template,)*
        #(#outputs,)*
        #(#inputs,)*
        #(out(#clobbers) _,)*
        #clobber_abi
        #options
      )
    })
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::ast::{id, lit_string, parse_tokens, punct, var};

  #[test]
  fn parse_template() {
    let template = "btsl %2,%1\n\tsbb %0,%0";
    let (rest, template_tokens) = Asm::parse_template(template).unwrap();

    assert!(rest.is_empty());
    assert_eq!(template_tokens, vec!["btsl {2},{1}", "sbb {0},{0}"]);
  }

  #[test]
  fn parse_asm() {
    parse_tokens!(
      Asm => [
        id!(__asm__),
        punct!("("),
        lit_string!("leal (%0,%0,4),%0"),
        punct!(":"),
        lit_string!("=r"),
        punct!("("),
        id!(n),
        punct!(")"),
        punct!(":"),
        lit_string!("0"),
        punct!("("),
        id!(n),
        punct!(")"),
        punct!(")")
      ],
      Asm {
        template: vec!["leal ({0},{0},4),{0}".into()],
        outputs: vec![(Dir::Out, RegConstraint::Reg, var!(n))],
        inputs: vec![(RegConstraint::Digit(0), var!(n))],
        clobbers: vec![]
      }
    );
  }

  #[test]
  fn parse_asm_memory_barrier() {
    parse_tokens!(
      Asm => [
        id!(__asm__),
        id!(volatile),
        punct!("("),
        lit_string!(""),
        punct!(":"),
        punct!(":"),
        punct!(":"),
        lit_string!("memory"),
        punct!(")")
      ],
      Asm { template: vec!["".into()], outputs: vec![], inputs: vec![], clobbers: vec!["memory".into()] }
    );
  }
}
