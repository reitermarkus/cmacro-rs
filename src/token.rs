use std::borrow::Cow;

use nom::{
  branch::alt,
  bytes::complete::{tag, take_until},
  character::complete::{char, none_of},
  combinator::{all_consuming, opt, recognize},
  multi::fold_many0,
  sequence::{delimited, pair},
};

use crate::ast::{escaped_char, LitCharPrefix};

/// A macro argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroArg {
  pub(crate) index: usize,
}

impl MacroArg {
  pub(crate) fn index(&self) -> usize {
    self.index
  }
}

/// A comment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment<'t> {
  pub(crate) comment: Cow<'t, str>,
}

impl<'t> TryFrom<&'t str> for Comment<'t> {
  type Error = nom::Err<nom::error::Error<&'t str>>;

  fn try_from(s: &'t str) -> Result<Self, Self::Error> {
    let (_, comment) = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(s)?;
    Ok(Self { comment: Cow::Borrowed(comment) })
  }
}

/// A string literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteral<'t> {
  literal: Cow<'t, str>,
}

impl<'t> TryFrom<&'t str> for StringLiteral<'t> {
  type Error = nom::Err<nom::error::Error<&'t str>>;

  fn try_from(s: &'t str) -> Result<Self, Self::Error> {
    let unquoted_string = fold_many0(alt((recognize(escaped_char), recognize(none_of("\\\"\n")))), || (), |_, _| ());
    let (_, literal) =
      all_consuming(recognize(pair(opt(LitCharPrefix::parse), delimited(char('\"'), unquoted_string, char('\"')))))(s)?;
    Ok(Self { literal: Cow::Borrowed(literal) })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn from_str_unescaped_quote() {
    StringLiteral::try_from(r#""ab"cd""#).unwrap_err();
  }

  #[test]
  fn from_str_not_a_string() {
    StringLiteral::try_from(r#"'c'"#).unwrap_err();
    StringLiteral::try_from(r#"1234"#).unwrap_err();
    StringLiteral::try_from(r#"3.14"#).unwrap_err();
    StringLiteral::try_from(r#"id"#).unwrap_err();
  }

  #[test]
  fn from_str() {
    StringLiteral::try_from(r#""string""#).unwrap();
  }

  #[test]
  fn from_str_utf8() {
    StringLiteral::try_from(r#"u8"string""#).unwrap();
  }

  #[test]
  fn from_str_utf16() {
    StringLiteral::try_from(r#"u"string""#).unwrap();
  }

  #[test]
  fn from_str_utf32() {
    StringLiteral::try_from(r#"U"string""#).unwrap();
  }

  #[test]
  fn from_str_wide() {
    StringLiteral::try_from(r#"L"string""#).unwrap();
  }

  #[test]
  fn from_str_escaped() {
    StringLiteral::try_from(r#""\360""#).unwrap();
    StringLiteral::try_from(r#""escaped\"quote""#).unwrap();
    StringLiteral::try_from(r#"u8"🎧\xf0\x9f\x8e\xa4""#).unwrap();
    StringLiteral::try_from(r#"u"🎧\uD83C\uDFA4""#).unwrap();
  }
}
