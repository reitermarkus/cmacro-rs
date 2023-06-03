use std::{fmt::Debug, ops::RangeFrom, str};

use nom::{
  branch::alt,
  bytes::complete::tag_no_case,
  character::{
    complete::{anychar, char, none_of, one_of},
    is_hex_digit, is_oct_digit,
  },
  combinator::{all_consuming, map, map_opt, value, verify},
  multi::fold_many_m_n,
  sequence::preceded,
  AsChar, Compare, FindToken, IResult, InputIter, InputLength, InputTake, Slice,
};
use proc_macro2::TokenStream;
use quote::TokenStreamExt;

use crate::{CodegenContext, LocalContext, MacroToken, Type};

mod char;
pub use self::char::*;
mod float;
pub use self::float::*;
mod int;
pub use self::int::*;
mod string;
pub use self::string::*;

/// A literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit<'t> {
  /// A character literal.
  Char(LitChar),
  /// A string literal.
  String(LitString<'t>),
  /// A floating-point literal.
  Float(LitFloat),
  /// An integer literal.
  Int(LitInt),
}

impl From<f32> for Lit<'_> {
  fn from(f: f32) -> Self {
    Lit::Float(LitFloat::Float(f))
  }
}

impl From<f64> for Lit<'_> {
  fn from(f: f64) -> Self {
    Lit::Float(LitFloat::Double(f))
  }
}

impl From<i32> for Lit<'_> {
  fn from(n: i32) -> Self {
    Lit::Int(LitInt { value: n.into(), suffix: None })
  }
}

impl<'t> Lit<'t> {
  pub(crate) fn parse_str(input: &'t str) -> IResult<&'t str, Self> {
    alt((
      map(LitChar::parse_str, Self::Char),
      map(LitString::parse_str, Self::String),
      map(LitFloat::parse_str, Self::Float),
      map(LitInt::parse_str, Self::Int),
    ))(input)
  }

  /// Parse a literal.
  pub fn parse<'i>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    alt((
      map(LitChar::parse, Self::Char),
      map(LitString::parse, Self::String),
      map(LitFloat::parse, Self::Float),
      map(LitInt::parse, Self::Int),
    ))(input)
  }

  pub(crate) fn finish<C: CodegenContext>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError> {
    match self {
      Self::Char(c) => c.finish(ctx),
      Self::String(s) => s.finish(ctx),
      Self::Float(f) => f.finish(ctx),
      Self::Int(i) => i.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Char(c) => c.to_tokens(ctx, tokens),
      Self::String(s) => {
        let (_, s) = s.to_token_stream(ctx, false);
        tokens.append_all(s)
      },
      Self::Float(f) => f.to_tokens(ctx, tokens),
      Self::Int(i) => i.to_tokens(ctx, tokens),
    }
  }

  pub(crate) fn into_static(self) -> Lit<'static> {
    match self {
      Self::Char(c) => Lit::Char(c),
      Self::String(s) => Lit::String(s.into_static()),
      Self::Float(f) => Lit::Float(f),
      Self::Int(i) => Lit::Int(i),
    }
  }
}

impl<'t> TryFrom<&'t str> for Lit<'t> {
  type Error = nom::Err<nom::error::Error<&'t str>>;

  fn try_from(s: &'t str) -> Result<Self, Self::Error> {
    let (_, lit) = all_consuming(Self::parse_str)(s)?;
    Ok(lit)
  }
}

/// Parse a simple escape sequence, e.g. `\n` (without the leading `\`).
fn simple_escape_sequence<I>(input: I) -> IResult<I, char>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  alt((
    value('\x07', char('a')),
    value('\x08', char('b')),
    value('\x1b', char('e')),
    value('\x0c', char('f')),
    value('\n', char('n')),
    value('\r', char('r')),
    value('\t', char('t')),
    value('\x0b', char('v')),
    one_of(r#"\'"?"#),
  ))(input)
}

/// Parse a numeric escape sequence, e.g. `\0` or `\xff` (without the leading `\`).
fn numeric_escape_sequence<I>(input: I) -> IResult<I, u32>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  alt((
    fold_many_m_n(
      1,
      3,
      map_opt(verify(anychar, |c| is_oct_digit(*c as u8)), |c| c.to_digit(8)),
      || 0,
      |acc, n| acc * 8 + n,
    ),
    preceded(
      tag_no_case("x"),
      fold_many_m_n(
        2,
        2,
        map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(16)),
        || 0,
        |acc, n| acc * 16 + n,
      ),
    ),
  ))(input)
}

/// Parse a universal character, e.g. `\U0001f34c` (without the leading `\`).
pub(crate) fn universal_char<I>(input: I) -> IResult<I, u32>
where
  I: Debug + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone,
  <I as InputIter>::Item: AsChar,
{
  alt((
    preceded(
      char('u'),
      fold_many_m_n(
        4,
        4,
        map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(16)),
        || 0,
        |acc, n| acc * 16 + n,
      ),
    ),
    preceded(
      char('U'),
      fold_many_m_n(
        8,
        8,
        map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(16)),
        || 0,
        |acc, n| acc * 16 + n,
      ),
    ),
  ))(input)
}

/// Parse an escaped character.
pub(crate) fn escaped_char<I>(input: I) -> IResult<I, u32>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  preceded(char('\\'), alt((map(simple_escape_sequence, u32::from), numeric_escape_sequence, universal_char)))(input)
}

/// Parse an unescaped character.
pub(crate) fn unescaped_char<I>(input: I) -> IResult<I, char>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  map(none_of("\\\'\n"), |b| b.as_char())(input)
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::BuiltInType;

  #[test]
  fn parse_int_before_float() {
    assert_eq!(Lit::try_from("123"), Ok(Lit::Int(LitInt { value: 123, suffix: None })));

    assert_eq!(Lit::try_from("123L"), Ok(Lit::Int(LitInt { value: 123, suffix: Some(BuiltInType::Long) })));
  }
}
