use std::{
  fmt::Debug,
  ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
  str,
};

use nom::{
  branch::alt,
  bytes::complete::{is_a, tag, tag_no_case},
  character::complete::{digit1, hex_digit1, oct_digit1},
  combinator::{all_consuming, cond, eof, map, map_opt, map_parser, opt, success, value},
  sequence::{delimited, pair, preceded},
  AsChar, Compare, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Slice,
};
use proc_macro2::TokenStream;
use quote::ToTokens;

use crate::{
  ast::tokens::{macro_token, meta, token},
  BuiltInType, CodegenContext, LocalContext, MacroToken, Type,
};

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

  fn from_str<I, C>(input: I) -> IResult<I, (i128, Option<&'static str>, Option<&'static str>)>
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

    let (input, (n, (unsigned, size))) = pair(digits, Self::parse_suffix)(input)?;
    Ok((input, (n, unsigned, size)))
  }

  fn parse_suffix<I, C>(input: I) -> IResult<I, (Option<&'static str>, Option<&'static str>)>
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
      map(
        pair(
          value("u", tag_no_case("u")),
          opt(alt((value("ll", tag_no_case("ll")), value("l", tag_no_case("l")), value("z", tag_no_case("z"))))),
        ),
        |(unsigned, size)| (Some(unsigned), size),
      ),
      map(
        pair(
          alt((value("ll", tag_no_case("ll")), value("l", tag_no_case("l")), value("z", tag_no_case("z")))),
          opt(value("u", tag_no_case("u"))),
        ),
        |(size, unsigned)| (unsigned, Some(size)),
      ),
      value((None, None), eof),
    )))(input)
  }

  /// Parse an integer literal.
  pub fn parse<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, input) = macro_token(tokens)?;

    let (_, (value, unsigned1, size1)) = Self::from_str(input).map_err(|err| err.map_input(|_| tokens))?;

    let suffix_unsigned = |tokens| alt((token("u"), token("U")))(tokens);
    let suffix_long = |tokens| alt((token("l"), token("L")))(tokens);
    let suffix_long_long = |tokens| alt((token("ll"), token("LL")))(tokens);
    let suffix_size_t = |tokens| alt((token("z"), token("Z")))(tokens);

    let mut suffix = alt((
      alt((
        map(
          pair(
            cond(unsigned1.is_none(), preceded(delimited(meta, token("##"), meta), suffix_unsigned)),
            cond(
              size1.is_none(),
              opt(preceded(delimited(meta, token("##"), meta), alt((suffix_long_long, suffix_long, suffix_size_t)))),
            ),
          ),
          |(unsigned, size)| (unsigned, size.flatten()),
        ),
        map(
          pair(
            cond(
              size1.is_none(),
              preceded(delimited(meta, token("##"), meta), alt((suffix_long_long, suffix_long, suffix_size_t))),
            ),
            cond(unsigned1.is_none(), opt(preceded(delimited(meta, token("##"), meta), suffix_unsigned))),
          ),
          |(size, unsigned)| (unsigned.flatten(), size),
        ),
        map_opt(
          cond(
            unsigned1.is_none() && size1.is_none(),
            preceded(
              delimited(meta, token("##"), meta),
              map_parser(macro_token, |token: &'i str| {
                Self::parse_suffix(token).map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))
              }),
            ),
          ),
          |opt| opt,
        ),
      )),
      success((None, None)),
    ));

    let (tokens, (unsigned2, size2)) = suffix(tokens)?;
    let unsigned = unsigned1.or(unsigned2).is_some();
    let size = size1.or(size2);

    let suffix = match (unsigned, size) {
      (false, None) => None,
      (true, None) => Some(BuiltInType::UInt),
      (unsigned, Some(size)) => {
        if size.eq_ignore_ascii_case("l") {
          Some(if unsigned { BuiltInType::ULong } else { BuiltInType::Long })
        } else if size.eq_ignore_ascii_case("ll") {
          Some(if unsigned { BuiltInType::ULongLong } else { BuiltInType::LongLong })
        } else {
          None
        }
      },
    };

    // TODO: Handle suffix.
    Ok((tokens, Self { value, suffix }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, _ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
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

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_set::tokens;

  #[test]
  fn parse_int_llu() {
    let (_, id) = LitInt::parse(tokens!["1", "##", "LL", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });
  }

  #[test]
  fn parse_int() {
    let (_, id) = LitInt::parse(tokens![r#"777"#]).unwrap();
    assert_eq!(id, LitInt { value: 777, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"0777"#]).unwrap();
    assert_eq!(id, LitInt { value: 0o777, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"8718937817238719"#]).unwrap();
    assert_eq!(id, LitInt { value: 8718937817238719, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"1U"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::UInt) });

    let (_, id) = LitInt::parse(tokens!["1", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::UInt) });

    let (_, id) = LitInt::parse(tokens![r#"3L"#]).unwrap();
    assert_eq!(id, LitInt { value: 3, suffix: Some(BuiltInType::Long) });

    let (_, id) = LitInt::parse(tokens![r#"1ULL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens!["1", "##", "U", "##", "LL"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens!["1", "##", "ULL"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens![r#"1UL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULong) });

    let (_, id) = LitInt::parse(tokens![r#"1LLU"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens!["1", "##", "LL", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens!["1", "##", "LLU"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(tokens![r#"1z"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: None });

    let (_, id) = LitInt::parse(tokens!["1", "##", "z"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"28Z"#]).unwrap();
    assert_eq!(id, LitInt { value: 28, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"0xff"#]).unwrap();
    assert_eq!(id, LitInt { value: 0xff, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"0XFF"#]).unwrap();
    assert_eq!(id, LitInt { value: 0xff, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"0b101"#]).unwrap();
    assert_eq!(id, LitInt { value: 0b101, suffix: None });

    let (_, id) = LitInt::parse(tokens![r#"0B1100"#]).unwrap();
    assert_eq!(id, LitInt { value: 0b1100, suffix: None });
  }

  #[test]
  fn rest() {
    let tokens = tokens![r#"0"#];
    let (rest, id) = LitInt::parse(tokens).unwrap();
    assert_eq!(id, LitInt { value: 0, suffix: None });
    assert!(rest.is_empty());
  }
}
