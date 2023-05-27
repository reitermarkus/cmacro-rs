use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  branch::alt,
  character::complete::{anychar, char},
  combinator::{all_consuming, map, map_opt, map_parser},
  multi::{fold_many0, fold_many1},
  sequence::{delimited, preceded},
  AsChar, IResult, InputIter, InputLength, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  literal::universal_char,
  tokens::{meta, take_one, token},
  Type,
};
use crate::{CodegenContext, LocalContext, ParseContext};

pub(crate) fn identifier_arg<I>(tokens: &[I]) -> IResult<&[I], LitIdent>
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

        let mut start = chars.next()?;

        if start == '$' {
          start = chars.next()?;

          if (unicode_ident::is_xid_start(start) || start == '_') && chars.all(unicode_ident::is_xid_continue) {
            return Some(LitIdent { id: s[1..].to_owned() })
          }
        }

        None
      },
    )(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
  })(tokens)
}

pub(crate) fn identifier_lit<I>(tokens: &[I]) -> IResult<&[I], LitIdent>
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

        let mut start = chars.next()?;
        let mut macro_arg = false;
        let mut offset = 0;

        if start == '$' {
          start = chars.next()?;
          offset = 1;
          macro_arg = true;
        }

        if (unicode_ident::is_xid_start(start) || start == '_') && chars.all(unicode_ident::is_xid_continue) {
          Some(LitIdent { id: s[offset..].to_owned() })
        } else {
          None
        }
      },
    )(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
  })(tokens)
}

pub(crate) fn concat_identifier_arg<I>(tokens: &[I]) -> IResult<&[I], LitIdent>
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

        let mut start = chars.next()?;

        if start == '$' {
          if chars.all(unicode_ident::is_xid_continue) {
            return Some(LitIdent { id: s[1..].to_owned() })
          }
        }

        {
          None
        }
      },
    ))(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
  })(tokens)
}

fn concat_identifier<I>(tokens: &[I]) -> IResult<&[I], LitIdent>
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
          Some(LitIdent { id: s })
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
}

impl LitIdent {
  /// Get the string representation of this identifier.
  pub fn as_str(&self) -> &str {
    &self.id
  }
}

impl LitIdent {
  /// Parse an identifier.
  pub(crate) fn parse<'i, 't>(tokens: &'i [&'t str], _ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    identifier_lit(tokens)
  }

  /// Parse an identifier.
  pub(crate) fn parse_concat<'i, 't>(tokens: &'i [&'t str], _ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    concat_identifier(tokens)
  }
}

impl From<&str> for LitIdent {
  fn from(s: &str) -> Self {
    Self { id: s.to_owned() }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const CTX: ParseContext = ParseContext::var_macro("IDENTIFIER");

  #[test]
  fn parse_literal() {
    let (_, id) = LitIdent::parse(&["asdf"], &CTX).unwrap();
    assert_eq!(id, "asdf".into());

    let (_, id) = LitIdent::parse(&["Δx"], &CTX).unwrap();
    assert_eq!(id, "Δx".into());

    let (_, id) = LitIdent::parse(&["_123"], &CTX).unwrap();
    assert_eq!(id, "_123".into());

    let (_, id) = LitIdent::parse(&["__INT_MAX__"], &CTX).unwrap();
    assert_eq!(id, "__INT_MAX__".into());
  }

  #[test]
  fn parse_wrong() {
    let res = LitIdent::parse(&["123def"], &CTX);
    assert!(res.is_err());

    let res = LitIdent::parse(&["123", "##", "def"], &CTX);
    assert!(res.is_err());
  }
}
