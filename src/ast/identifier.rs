use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::{anychar, char},
  combinator::{all_consuming, map_opt, map_parser},
  multi::fold_many1,
  sequence::preceded,
  IResult,
};

use super::{
  literal::universal_char,
  tokens::{macro_token},
};
use crate::{MacroToken, ParseContext};

pub(crate) fn identifier_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent> {
  map_parser(macro_token, |token: Cow<'t, str>| {
    let (_, id) = map_opt(
      all_consuming(|token| {
        fold_many1(
          alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
          String::new,
          |mut acc, c| {
            acc.push(c);
            acc
          },
        )(token)
      }),
      |s| {
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
    )(token.as_ref())
    .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

    Ok((Cow::Borrowed(""), id))
  })(tokens)
}

pub(crate) fn is_identifier(s: &str) -> bool {
  let mut chars = s.chars();

  if let Some(first_character) = chars.next() {
    return (unicode_ident::is_xid_start(first_character) || first_character == '_')
      && chars.all(unicode_ident::is_xid_continue)
  }

  false
}

pub(crate) fn identifier_lit<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent> {
  map_parser(macro_token, |token: Cow<'t, str>| {
    let (_, id) = map_opt(
      all_consuming(|token| {
        fold_many1(
          alt((map_opt(preceded(char('\\'), universal_char), char::from_u32), anychar)),
          String::new,
          |mut acc, c| {
            acc.push(c);
            acc
          },
        )(token)
      }),
      |s| {
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
    )(token.as_ref())
    .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

    Ok((Cow::Borrowed(""), id))
  })(tokens)
}

pub(crate) fn concat_identifier_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent> {
  map_parser(macro_token, |token: Cow<'t, str>| {
    let (_, id) = all_consuming(map_opt(
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

        let start = chars.next()?;

        if start == '$' && chars.all(unicode_ident::is_xid_continue) {
          return Some(LitIdent { id: s[1..].to_owned() })
        }

        {
          None
        }
      },
    ))(token.as_ref())
    .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

    Ok((Cow::Borrowed(""), id))
  })(tokens)
}

fn concat_identifier<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], LitIdent> {
  map_parser(macro_token, |token: Cow<'t, str>| {
    let (_, id) = all_consuming(map_opt(
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
          Some(LitIdent { id: s })
        } else {
          None
        }
      },
    ))(token.as_ref())
    .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

    Ok((Cow::Borrowed(""), id))
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
  pub(crate) fn parse<'i, 't>(
    tokens: &'i [MacroToken<'t>],
    _ctx: &ParseContext<'_>,
  ) -> IResult<&'i [MacroToken<'t>], Self> {
    identifier_lit(tokens)
  }

  /// Parse an identifier.
  pub(crate) fn parse_concat<'i, 't>(
    tokens: &'i [MacroToken<'t>],
    _ctx: &ParseContext<'_>,
  ) -> IResult<&'i [MacroToken<'t>], Self> {
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

  use crate::macro_set::tokens;

  const CTX: ParseContext = ParseContext::var_macro("IDENTIFIER");

  #[test]
  fn parse_literal() {
    let (_, id) = LitIdent::parse(tokens!["asdf"], &CTX).unwrap();
    assert_eq!(id, "asdf".into());

    let (_, id) = LitIdent::parse(tokens!["Δx"], &CTX).unwrap();
    assert_eq!(id, "Δx".into());

    let (_, id) = LitIdent::parse(tokens!["_123"], &CTX).unwrap();
    assert_eq!(id, "_123".into());

    let (_, id) = LitIdent::parse(tokens!["__INT_MAX__"], &CTX).unwrap();
    assert_eq!(id, "__INT_MAX__".into());
  }

  #[test]
  fn parse_wrong() {
    let tokens = tokens!["123def"];
    let res = LitIdent::parse(tokens, &CTX);
    assert!(res.is_err());

    let tokens = tokens!["123", "##", "def"];
    let res = LitIdent::parse(tokens, &CTX);
    assert!(res.is_err());
  }
}
