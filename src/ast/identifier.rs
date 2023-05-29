use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::{anychar, char},
  combinator::map_opt,
  multi::fold_many1,
  sequence::preceded,
  IResult,
};

use super::{literal::universal_char, tokens::map_token};
use crate::MacroToken;

pub(crate) fn is_identifier(s: &str) -> bool {
  let mut chars = s.chars();

  if let Some(first_character) = chars.next() {
    return (unicode_ident::is_xid_start(first_character) || first_character == '_')
      && chars.all(unicode_ident::is_xid_continue)
  }

  false
}

pub(crate) fn identifier_lit<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent<'t>> {
  map_token(map_opt(
    |token| {
      fold_many1(
        alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
        String::new,
        |mut acc, c| {
          acc.push(c);
          acc
        },
      )(token)
    },
    |s| {
      if is_identifier(&s) {
        Some(LitIdent { id: Cow::Owned(s) })
      } else {
        None
      }
    },
  ))(tokens)
}

fn concat_identifier<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent<'t>> {
  map_token(map_opt(
    fold_many1(
      alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
      String::new,
      |mut acc, c| {
        acc.push(c);
        acc
      },
    ),
    |s| {
      let mut chars = s.chars();

      if chars.all(unicode_ident::is_xid_continue) {
        Some(LitIdent { id: Cow::Owned(s) })
      } else {
        None
      }
    },
  ))(tokens)
}

/// A literal identifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitIdent<'t> {
  pub(crate) id: Cow<'t, str>,
}

impl<'t> LitIdent<'t> {
  /// Get the string representation of this identifier.
  pub fn as_str(&self) -> &str {
    self.id.as_ref()
  }

  /// Parse an identifier.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    identifier_lit(tokens)
  }

  /// Parse an identifier.
  pub(crate) fn parse_concat<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    concat_identifier(tokens)
  }

  pub(crate) fn to_static(&self) -> LitIdent<'static> {
    LitIdent { id: Cow::Owned(self.id.clone().into_owned()) }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::{lit_id, macro_set::tokens};

  #[test]
  fn parse_literal() {
    let (_, id) = LitIdent::parse(tokens!["asdf"]).unwrap();
    assert_eq!(id, lit_id!(asdf));

    let (_, id) = LitIdent::parse(tokens!["Δx"]).unwrap();
    assert_eq!(id, lit_id!(Δx));

    let (_, id) = LitIdent::parse(tokens!["_123"]).unwrap();
    assert_eq!(id, lit_id!(_123));

    let (_, id) = LitIdent::parse(tokens!["__INT_MAX__"]).unwrap();
    assert_eq!(id, lit_id!(__INT_MAX__));
  }

  #[test]
  fn parse_wrong() {
    let tokens = tokens!["123def"];
    let res = LitIdent::parse(tokens);
    assert!(res.is_err());

    let tokens = tokens!["123", "##", "def"];
    let res = LitIdent::parse(tokens);
    assert!(res.is_err());
  }
}
