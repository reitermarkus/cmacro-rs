use std::{fmt::Debug, ops::RangeFrom, str};

use nom::{
  branch::alt,
  bytes::complete::tag_no_case,
  character::{
    complete::{anychar, char, none_of, one_of},
    is_hex_digit, is_oct_digit,
  },
  combinator::{map, map_opt, value, verify},
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
pub enum Lit {
  /// A character literal.
  Char(LitChar),
  /// A string literal.
  String(LitString),
  /// A floating-point literal.
  Float(LitFloat),
  /// An integer literal.
  Int(LitInt),
}

impl From<f32> for Lit {
  fn from(f: f32) -> Lit {
    Lit::Float(LitFloat::Float(f))
  }
}

impl From<f64> for Lit {
  fn from(f: f64) -> Lit {
    Lit::Float(LitFloat::Double(f))
  }
}

impl From<char> for Lit {
  fn from(c: char) -> Lit {
    let c = c as u32;

    if c <= 0xff {
      Lit::Char(LitChar::Ordinary(c as u8))
    } else {
      panic!()
    }
  }
}

impl From<i32> for Lit {
  fn from(n: i32) -> Lit {
    Lit::Int(LitInt { value: n.into(), suffix: None })
  }
}

impl Lit {
  /// Parse a literal.
  pub fn parse<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    alt((
      map(LitChar::parse, Self::Char),
      map(LitString::parse, Self::String),
      map(LitFloat::parse, Self::Float),
      map(LitInt::parse, Self::Int),
    ))(input)
  }

  pub(crate) fn finish<'t, C>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
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

  use crate::macro_set::tokens;

  use crate::BuiltInType;

  #[test]
  fn parse_int_before_float() {
    let (_, int) = Lit::parse(tokens!["123"]).unwrap();
    assert_eq!(int, Lit::Int(LitInt { value: 123, suffix: None }));

    let (_, int) = Lit::parse(tokens!["123L"]).unwrap();
    assert_eq!(int, Lit::Int(LitInt { value: 123, suffix: Some(BuiltInType::Long) }));
  }
}
