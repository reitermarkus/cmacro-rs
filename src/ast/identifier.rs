use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  branch::alt,
  character::complete::{anychar, char},
  combinator::{all_consuming, map, map_opt, map_parser},
  multi::{fold_many0, fold_many1},
  sequence::{delimited, preceded},
  AsChar, Compare, FindSubstring, IResult, InputIter, InputLength, InputTake, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  literal::universal_char,
  tokens::{meta, take_one, token},
  Type,
};
use crate::{CodegenContext, LocalContext, MacroArgType, ParseContext};

pub(crate) fn identifier<I>(tokens: &[I]) -> IResult<&[I], String>
where
  I: Debug + InputLength + InputIter + Slice<RangeFrom<usize>> + Clone,
  <I as InputIter>::Item: AsChar,
{
  map_parser(take_one, |token| {
    map_opt(
      all_consuming(|token| {
        fold_many1(
          alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
          Vec::new,
          |mut acc, c| {
            acc.push(c);
            acc
          },
        )(token)
      }),
      |c| {
        let s: Option<Vec<u8>> = c.iter().map(|c| if *c as u32 <= 0xff { Some(*c as u8) } else { None }).collect();
        let s =
          if let Some(s) = s.and_then(|s| String::from_utf8(s).ok()) { s } else { c.into_iter().collect::<String>() };

        let mut chars = s.chars();
        let start = chars.next()?;
        if (unicode_ident::is_xid_start(start) || start == '_') && chars.all(unicode_ident::is_xid_continue) {
          Some(s)
        } else {
          None
        }
      },
    )(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
  })(tokens)
}

fn concat_identifier<I>(tokens: &[I]) -> IResult<&[I], String>
where
  I: Debug + InputLength + InputIter + Slice<RangeFrom<usize>> + Clone,
  <I as InputIter>::Item: AsChar,
{
  map_parser(take_one, |token| {
    all_consuming(map_opt(
      fold_many1(
        alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
        Vec::new,
        |mut acc, c| {
          acc.push(c);
          acc
        },
      ),
      |c| {
        let s: Option<Vec<u8>> = c.iter().map(|c| if *c as u32 <= 0xff { Some(*c as u8) } else { None }).collect();
        let s =
          if let Some(s) = s.and_then(|s| String::from_utf8(s).ok()) { s } else { c.into_iter().collect::<String>() };

        let mut chars = s.chars();
        if chars.all(unicode_ident::is_xid_continue) {
          Some(s)
        } else {
          None
        }
      },
    ))(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
  })(tokens)
}

/// A literal identifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitIdent {
  pub(crate) id: String,
  pub(crate) macro_arg: bool,
}

impl LitIdent {
  /// Get the string representation of this identifier.
  pub fn as_str(&self) -> &str {
    &self.id
  }
}

impl From<&str> for LitIdent {
  fn from(s: &str) -> Self {
    Self { id: s.to_owned(), macro_arg: false }
  }
}

/// An identifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Identifier {
  /// A literal identifier.
  ///
  /// ```c
  /// #define ID asdf
  /// ```
  Literal(LitIdent),
  /// A concatenated identifier.
  ///
  /// ```c
  /// #define ID abc ## def
  /// #define ID abc ## 123
  /// ```
  Concat(Vec<LitIdent>),
}

impl Identifier {
  /// Parse an identifier.
  pub(crate) fn parse<'i, I, C>(tokens: &'i [I], ctx: &ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputIter<Item = C>
      + InputTake
      + InputLength
      + Compare<&'static str>
      + Slice<std::ops::RangeFrom<usize>>
      + FindSubstring<&'static str>
      + Clone,
    C: AsChar,
  {
    fn map_raw_ident(id: String, ctx: &ParseContext<'_>) -> LitIdent {
      let arg = if id == "__VA_ARGS__" { "..." } else { id.as_str() };
      let macro_arg = ctx.args.contains(&arg);
      LitIdent { id, macro_arg }
    }

    let (tokens, id) = map(identifier, |id| Self::Literal(map_raw_ident(id, ctx)))(tokens)?;

    fold_many0(
      preceded(delimited(meta::<I>, token::<I>("##"), meta::<I>), map(concat_identifier, |id| map_raw_ident(id, ctx))),
      move || id.clone(),
      |acc, item| match acc {
        Self::Literal(mut id) => {
          if !id.macro_arg && !item.macro_arg {
            id.id.push_str(item.as_str());
            Self::Literal(id)
          } else {
            Self::Concat(vec![id, item])
          }
        },
        Self::Concat(mut ids) => {
          if let Some(last) = ids.last_mut() {
            if !last.macro_arg && !item.macro_arg {
              last.id.push_str(item.as_str());
              return Self::Concat(ids)
            }
          }

          ids.push(item);
          Self::Concat(ids)
        },
      },
    )(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    if let Self::Concat(ref mut ids) = self {
      for id in ids {
        if id.macro_arg {
          if let Some(arg_type) = ctx.arg_type_mut(id.as_str()) {
            *arg_type = MacroArgType::Ident;
          }
        }
      }
    }

    // An identifier does not have a type.
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    match self {
      Self::Literal(ref id) => {
        if id.as_str().is_empty() {
          return quote! {}
        }

        if id.as_str() == "__VA_ARGS__" {
          return quote! { $($__VA_ARGS__),* }
        }

        let name = Ident::new(id.as_str(), Span::call_site());

        if ctx.export_as_macro && id.macro_arg {
          quote! { $#name }
        } else {
          quote! { #name }
        }
      },
      Self::Concat(ids) => {
        let trait_prefix = ctx.trait_prefix();

        let ids = ids.iter().map(|id| Self::Literal(id.to_owned()).to_token_stream(ctx));
        quote! { #trait_prefix concat_idents!(#(#ids),*) }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const CTX: ParseContext = ParseContext::var_macro("IDENTIFIER");

  #[test]
  fn parse_literal() {
    let (_, id) = Identifier::parse(&["asdf"], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("asdf".into()));

    let (_, id) = Identifier::parse(&["Δx"], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("Δx".into()));

    let (_, id) = Identifier::parse(&["Δx".as_bytes()], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("Δx".into()));

    let (_, id) = Identifier::parse(&["_123"], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("_123".into()));

    let (_, id) = Identifier::parse(&["__INT_MAX__"], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("__INT_MAX__".into()));
  }

  #[test]
  fn parse_concat() {
    let ctx = ParseContext::fn_macro("IDENTIFIER", &["abc"]);

    let (_, id) = Identifier::parse(&["abc", "##", "def"], &ctx).unwrap();
    assert_eq!(id, Identifier::Concat(vec![LitIdent { id: "abc".into(), macro_arg: true }, "def".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "def", "##", "ghi"], &ctx).unwrap();
    assert_eq!(id, Identifier::Concat(vec![LitIdent { id: "abc".into(), macro_arg: true }, "defghi".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "_def"], &ctx).unwrap();
    assert_eq!(id, Identifier::Concat(vec![LitIdent { id: "abc".into(), macro_arg: true }, "_def".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "123"], &ctx).unwrap();
    assert_eq!(id, Identifier::Concat(vec![LitIdent { id: "abc".into(), macro_arg: true }, "123".into()]));

    let (_, id) = Identifier::parse(&["__INT", "##", "_MAX__"], &CTX).unwrap();
    assert_eq!(id, Identifier::Literal("__INT_MAX__".into()));
  }

  #[test]
  fn parse_wrong() {
    let res = Identifier::parse(&["123def"], &CTX);
    assert!(res.is_err());

    let res = Identifier::parse(&["123", "##", "def"], &CTX);
    assert!(res.is_err());
  }
}
