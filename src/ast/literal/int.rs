use std::{
  fmt::Debug,
  ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
  str,
};

use nom::{
  branch::alt,
  bytes::complete::{is_a, tag, tag_no_case},
  character::complete::{digit1, hex_digit1, oct_digit1},
  combinator::{all_consuming, eof, map, map_opt, opt, value},
  sequence::{pair, preceded},
  AsChar, Compare, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Slice,
};
use proc_macro2::TokenStream;
use quote::ToTokens;

use crate::{ast::tokens::take_one, BuiltInType, CodegenContext, Lit, LocalContext, MacroToken, Type};

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct LitIntUnsignedSuffix;

impl LitIntUnsignedSuffix {
  pub fn parse<I, C>(input: I) -> IResult<I, Self>
  where
    I: InputTake + InputIter<Item = C> + Compare<&'static str> + Clone,
    C: AsChar,
  {
    value(Self, tag_no_case("u"))(input)
  }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum LitIntSizeSuffix {
  LongLong,
  Long,
  SizeT,
}

impl LitIntSizeSuffix {
  pub fn parse<I, C>(input: I) -> IResult<I, Self>
  where
    I: InputTake + InputIter<Item = C> + Compare<&'static str> + Clone,
    C: AsChar,
  {
    alt((
      value(Self::LongLong, alt((tag("ll"), tag("LL")))),
      value(Self::Long, tag_no_case("l")),
      value(Self::SizeT, tag_no_case("z")),
    ))(input)
  }
}

/// An integer literal.
///
/// ```c
/// #define INT 1
/// #define INT 2ull
/// #define INT 3u ## LL
/// #define INT 4 ## ULL
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LitInt {
  /// The integer value.
  pub value: i128,
  /// The literal suffix, if any.
  pub suffix: Option<BuiltInType>,
}

impl LitInt {
  fn parse_i128<I>(base: u32) -> impl Fn(I) -> Option<i128>
  where
    I: Debug + InputIter,
    <I as InputIter>::Item: AsChar,
  {
    move |input| {
      let mut value = 0i128;

      for c in input.iter_elements() {
        let d = c.as_char().to_digit(base).unwrap();
        value = value.checked_mul(base as i128)?.checked_add(d as i128)?;
      }

      Some(value)
    }
  }

  fn parse_suffix<I, C>(input: I) -> IResult<I, (Option<LitIntUnsignedSuffix>, Option<LitIntSizeSuffix>)>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<std::ops::RangeFrom<usize>>
      + Compare<&'static str>
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Clone,
    C: AsChar,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    all_consuming(alt((
      map(pair(LitIntUnsignedSuffix::parse, opt(LitIntSizeSuffix::parse)), |(unsigned, size)| (Some(unsigned), size)),
      map(pair(LitIntSizeSuffix::parse, opt(LitIntUnsignedSuffix::parse)), |(size, unsigned)| (unsigned, Some(size))),
      value((None, None), eof),
    )))(input)
  }

  pub(crate) fn parse_str<I, C>(input: I) -> IResult<I, Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<std::ops::RangeFrom<usize>>
      + Compare<&'static str>
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Clone,
    C: AsChar,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let digits = alt((
      map_opt(preceded(tag_no_case("0x"), hex_digit1), Self::parse_i128(16)),
      map_opt(preceded(tag_no_case("0b"), is_a("01")), Self::parse_i128(2)),
      map_opt(preceded(tag("0"), oct_digit1), Self::parse_i128(8)),
      map_opt(digit1, Self::parse_i128(10)),
    ));

    let (input, (value, (unsigned, size))) = pair(digits, Self::parse_suffix)(input)?;

    let suffix = match (unsigned, size) {
      (None, None) => None,
      (Some(LitIntUnsignedSuffix), None) => Some(BuiltInType::UInt),
      (Some(LitIntUnsignedSuffix), Some(LitIntSizeSuffix::Long)) => Some(BuiltInType::ULong),
      (None, Some(LitIntSizeSuffix::Long)) => Some(BuiltInType::Long),
      (Some(LitIntUnsignedSuffix), Some(LitIntSizeSuffix::LongLong)) => Some(BuiltInType::ULongLong),
      (None, Some(LitIntSizeSuffix::LongLong)) => Some(BuiltInType::LongLong),
      (Some(LitIntUnsignedSuffix), Some(LitIntSizeSuffix::SizeT)) => Some(BuiltInType::SizeT),
      (None, Some(LitIntSizeSuffix::SizeT)) => Some(BuiltInType::SSizeT),
    };

    Ok((input, Self { value, suffix }))
  }

  /// Parse an integer literal.
  pub fn parse<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    map_opt(take_one, |token| if let MacroToken::Lit(Lit::Int(lit)) = token { Some(*lit) } else { None })(tokens)
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'t, C>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, _ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    let i = proc_macro2::Literal::i128_unsuffixed(self.value);
    i.to_tokens(tokens)
  }
}

impl Add for LitInt {
  type Output = Self;

  fn add(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_add(other.value);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Sub for LitInt {
  type Output = Self;

  fn sub(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_sub(other.value);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Mul for LitInt {
  type Output = Self;

  fn mul(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_mul(other.value);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Div for LitInt {
  type Output = Self;

  fn div(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_div(other.value);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Rem for LitInt {
  type Output = Self;

  fn rem(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_rem(other.value);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Shl<LitInt> for LitInt {
  type Output = Self;

  fn shl(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_shl(other.value.min(u32::MAX as i128) as u32);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl Shr<LitInt> for LitInt {
  type Output = Self;

  fn shr(self, other: Self) -> Self::Output {
    let value = self.value.wrapping_shr(other.value.min(u32::MAX as i128) as u32);
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl BitAnd for LitInt {
  type Output = Self;

  fn bitand(self, other: Self) -> Self::Output {
    let value = self.value & other.value;
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl BitOr for LitInt {
  type Output = Self;

  fn bitor(self, other: Self) -> Self::Output {
    let value = self.value | other.value;
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl BitXor for LitInt {
  type Output = Self;

  fn bitxor(self, other: Self) -> Self::Output {
    let value = self.value ^ other.value;
    let suffix = match (self.suffix, other.suffix) {
      (Some(s1), Some(s2)) if s1 == s2 => Some(s1),
      (s1, s2) => s1.xor(s2),
    };
    Self { value, suffix }
  }
}

impl<'t> TryFrom<&'t str> for LitInt {
  type Error = nom::Err<nom::error::Error<&'t str>>;

  fn try_from(s: &'t str) -> Result<Self, Self::Error> {
    let (_, lit) = all_consuming(Self::parse_str)(s)?;
    Ok(lit)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_int_u() {
    assert_eq!(LitInt::try_from("1U"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::UInt) }));

    assert_eq!(LitInt::try_from("1u"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::UInt) }));
  }

  #[test]
  fn parse_int_l() {
    assert_eq!(LitInt::try_from("3L"), Ok(LitInt { value: 3, suffix: Some(BuiltInType::Long) }));

    assert_eq!(LitInt::try_from("3l"), Ok(LitInt { value: 3, suffix: Some(BuiltInType::Long) }));
  }

  #[test]
  fn parse_int_ull() {
    assert_eq!(LitInt::try_from("1ULL"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));

    assert_eq!(LitInt::try_from("1Ull"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));

    assert_eq!(LitInt::try_from("1uLL"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));
  }

  #[test]
  fn parse_int_llu() {
    assert_eq!(LitInt::try_from("1LLU"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));

    assert_eq!(LitInt::try_from("1llU"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));

    assert_eq!(LitInt::try_from("1LLu"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) }));
  }

  #[test]
  fn parse_int_ul() {
    assert_eq!(LitInt::try_from("1UL"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULong) }));

    assert_eq!(LitInt::try_from("1Ul"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULong) }));

    assert_eq!(LitInt::try_from("1uL"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULong) }));

    assert_eq!(LitInt::try_from("1ul"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::ULong) }));
  }

  #[test]
  fn parse_int_ll() {
    assert_eq!(LitInt::try_from("1LL"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::LongLong) }));

    assert_eq!(LitInt::try_from("1ll"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::LongLong) }));

    LitInt::try_from("1Ll").unwrap_err();
    LitInt::try_from("1lL").unwrap_err();
  }

  #[test]
  fn parse_int_uz() {
    assert_eq!(LitInt::try_from("1UZ"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));

    assert_eq!(LitInt::try_from("1Uz"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));

    assert_eq!(LitInt::try_from("1uZ"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));
  }

  #[test]
  fn parse_int_zu() {
    assert_eq!(LitInt::try_from("1ZU"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));

    assert_eq!(LitInt::try_from("1Zu"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));

    assert_eq!(LitInt::try_from("1zU"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SizeT) }));

    assert_eq!(LitInt::try_from("28zu"), Ok(LitInt { value: 28, suffix: Some(BuiltInType::SizeT) }));
  }

  #[test]
  fn parse_int_z() {
    assert_eq!(LitInt::try_from("28Z"), Ok(LitInt { value: 28, suffix: Some(BuiltInType::SSizeT) }));

    assert_eq!(LitInt::try_from("1z"), Ok(LitInt { value: 1, suffix: Some(BuiltInType::SSizeT) }));
  }

  #[test]
  fn parse_int_oct() {
    assert_eq!(LitInt::try_from("0777"), Ok(LitInt { value: 0o777, suffix: None }));
  }

  #[test]
  fn parse_int_hex() {
    assert_eq!(LitInt::try_from("0xff"), Ok(LitInt { value: 0xff, suffix: None }));

    assert_eq!(LitInt::try_from("0XFF"), Ok(LitInt { value: 0xff, suffix: None }));
  }

  #[test]
  fn parse_int_binary() {
    assert_eq!(LitInt::try_from("0b101"), Ok(LitInt { value: 0b101, suffix: None }));

    assert_eq!(LitInt::try_from("0B1100"), Ok(LitInt { value: 0b1100, suffix: None }));
  }

  #[test]
  fn parse_int() {
    assert_eq!(LitInt::try_from("777"), Ok(LitInt { value: 777, suffix: None }));

    assert_eq!(LitInt::try_from("8718937817238719"), Ok(LitInt { value: 8718937817238719, suffix: None }));
  }
}
