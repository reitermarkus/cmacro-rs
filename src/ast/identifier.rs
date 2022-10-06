use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  branch::alt,
  character::complete::{anychar, char},
  combinator::{all_consuming, map_opt, map_parser},
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
use crate::{CodegenContext, LocalContext, MacroArgType};

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

/// An identifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Identifier {
  /// A literal identifier, e.g.
  ///
  /// ```c
  /// #define ID asdf
  /// ```
  Literal(String),
  /// A concatenated identifier, e.g.
  ///
  /// ```c
  /// #define ID abc ## def
  /// #define ID abc ## 123
  /// ```
  Concat(Vec<String>),
}

impl Identifier {
  /// Parse an identifier.
  pub fn parse<I, T>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputIter<Item = T>
      + InputTake
      + InputLength
      + Compare<&'static str>
      + Slice<std::ops::RangeFrom<usize>>
      + FindSubstring<&'static str>
      + Clone,
    T: AsChar,
  {
    let (tokens, id) = identifier(tokens)?;

    fold_many0(
      preceded(delimited(meta::<I>, token::<I>("##"), meta::<I>), concat_identifier),
      move || Self::Literal(id.clone()),
      |acc, item| match acc {
        Self::Literal(id) => Self::Concat(vec![id, item]),
        Self::Concat(mut ids) => {
          ids.push(item);
          Self::Concat(ids)
        },
      },
    )(tokens)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    if let Self::Concat(ref mut ids) = self {
      let mut new_ids = vec![];
      let mut non_arg_id: Option<String> = None;

      for id in ids {
        if let Some(arg_ty) = ctx.arg_type_mut(id.as_str()) {
          *arg_ty = MacroArgType::Ident;

          if let Some(non_arg_id) = non_arg_id.take() {
            new_ids.push(non_arg_id);
          }

          new_ids.push(id.to_owned());
        } else if let Some(ref mut non_arg_id) = non_arg_id {
          non_arg_id.push_str(id);
        } else {
          non_arg_id = Some(id.to_owned());
        }
      }

      if let Some(non_arg_id) = non_arg_id.take() {
        new_ids.push(non_arg_id);
      }

      if new_ids.len() == 1 {
        *self = Self::Literal(new_ids.remove(0));
      } else {
        *self = Self::Concat(new_ids);
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
      Self::Literal(ref s) => {
        if s.is_empty() {
          return quote! {}
        }

        if s == "__VA_ARGS__" {
          return quote! { $($__VA_ARGS__),* }
        }

        let id = Ident::new(s, Span::call_site());

        if ctx.export_as_macro && ctx.is_macro_arg(s) {
          quote! { $#id }
        } else {
          quote! { #id }
        }
      },
      Self::Concat(ids) => {
        let ids = ids.iter().map(|id| Self::Literal(id.to_owned()).to_token_stream(ctx));
        quote! { ::core::concat_idents!(#(#ids),*) }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_literal() {
    let (_, id) = Identifier::parse(&["asdf"]).unwrap();
    assert_eq!(id, Identifier::Literal("asdf".into()));

    let (_, id) = Identifier::parse(&["Δx"]).unwrap();
    assert_eq!(id, Identifier::Literal("Δx".into()));

    let (_, id) = Identifier::parse(&["Δx".as_bytes()]).unwrap();
    assert_eq!(id, Identifier::Literal("Δx".into()));

    let (_, id) = Identifier::parse(&["_123"]).unwrap();
    assert_eq!(id, Identifier::Literal("_123".into()));

    let (_, id) = Identifier::parse(&["__INT_MAX__"]).unwrap();
    assert_eq!(id, Identifier::Literal("__INT_MAX__".into()));
  }

  #[test]
  fn parse_concat() {
    let (_, id) = Identifier::parse(&["abc", "##", "def"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["abc".into(), "def".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "_def"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["abc".into(), "_def".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "123"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["abc".into(), "123".into()]));

    let (_, id) = Identifier::parse(&["__INT", "##", "_MAX__"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["__INT".into(), "_MAX__".into()]));
  }

  #[test]
  fn parse_wrong() {
    let res = Identifier::parse(&["123def"]);
    assert!(res.is_err());

    let res = Identifier::parse(&["123", "##", "def"]);
    assert!(res.is_err());
  }
}
