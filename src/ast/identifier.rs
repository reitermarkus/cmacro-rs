use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::{anychar, char, satisfy},
  combinator::{map, map_opt, recognize, verify},
  multi::{fold_many0},
  sequence::{pair, preceded},
  IResult,
};

use super::{literal::universal_char, tokens::map_token};
use crate::MacroToken;

fn is_identifier_start(c: char) -> bool {
  unicode_ident::is_xid_start(c) || c == '_'
}

pub(crate) fn is_identifier(s: &str) -> bool {
  let mut chars = s.chars();

  if let Some(first_character) = chars.next() {
    return is_identifier_start(first_character) && chars.all(unicode_ident::is_xid_continue)
  }

  false
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

  pub(crate) fn parse_str(input: &'t str) -> IResult<&'t str, Self> {
    alt((
      map(
        recognize(pair(
          satisfy(is_identifier_start),
          fold_many0(satisfy(unicode_ident::is_xid_continue), || (), |_, _| ()),
        )),
        |s| Self { id: Cow::Borrowed(s) },
      ),
      |token| {
        let mut identifier_char = alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar));

        let (token, start_char) = verify(&mut identifier_char, |c| is_identifier_start(*c))(token)?;

        fold_many0(
          verify(identifier_char, |c| unicode_ident::is_xid_continue(*c)),
          move || LitIdent { id: Cow::Owned(String::from(start_char)) },
          |mut id, c| {
            id.id.to_mut().push(c);
            id
          },
        )(token)
      },
    ))(input)
  }

  /// Parse an identifier.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    map_token(map(LitIdent::<'i>::parse_str, |id: LitIdent<'i>| id.to_static()))(tokens)
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

    let (_, id) = LitIdent::parse(tokens!("\\u0401")).unwrap();
    assert_eq!(id, lit_id!(Ё));

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
  }
}
