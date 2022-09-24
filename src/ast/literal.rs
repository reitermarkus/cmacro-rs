use std::ops::RangeFrom;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};
use std::str;

use nom::branch::alt;
use nom::character::complete::anychar;
use nom::combinator::verify;
use nom::multi::fold_many_m_n;
use nom::AsChar;
use nom::Compare;
use nom::FindToken;
use nom::InputIter;
use nom::InputLength;
use nom::InputTake;
use nom::InputTakeAtPosition;
use nom::Slice;

use nom::branch::permutation;
use nom::bytes::complete::is_not;
use nom::bytes::complete::{is_a, tag, tag_no_case};
use nom::character::complete::none_of;
use nom::character::complete::{char, digit1, hex_digit1, oct_digit1, one_of};
use nom::character::{is_hex_digit, is_oct_digit};
use nom::combinator::eof;
use nom::combinator::map_res;
use nom::combinator::recognize;
use nom::combinator::{all_consuming, cond, map_opt};
use nom::combinator::{map, opt, value};
use nom::multi::fold_many0;
use nom::multi::fold_many1;
use nom::sequence::delimited;
use nom::sequence::pair;
use nom::sequence::preceded;
use nom::sequence::separated_pair;
use nom::sequence::terminated;
use nom::AsBytes;
use nom::IResult;
use proc_macro2::TokenStream;
use quote::quote;
use quote::{ToTokens, TokenStreamExt};
use std::num::FpCategory;

use super::{
  tokens::{meta, take_one, token},
  ty::BuiltInType,
};
use crate::{CodegenContext, LocalContext};

/// A literal.
///
/// Also see [`LitChar`], [`LitString`], [`LitFloat`] and [`LitInt`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
  Char(LitChar),
  String(LitString),
  Float(LitFloat),
  Int(LitInt),
}

impl Lit {
  pub fn parse<'i, 't>(input: &'i [&'t [u8]]) -> IResult<&'i [&'t [u8]], Self> {
    alt((
      map(LitChar::parse, Self::Char),
      map(LitString::parse, Self::String),
      map(LitFloat::parse, Self::Float),
      map(LitInt::parse, Self::Int),
    ))(input)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Char(c) => c.to_tokens(ctx, tokens),
      Self::String(s) => s.to_tokens(ctx, tokens),
      Self::Float(f) => f.to_tokens(ctx, tokens),
      Self::Int(i) => i.to_tokens(ctx, tokens),
    }
  }
}

fn escaped_char<I>(input: I) -> IResult<I, Vec<u8>>
where
  I: InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  alt((
    map(char('a'), |_| vec![b'\x07']),
    map(char('b'), |_| vec![b'\x08']),
    map(char('e'), |_| vec![b'\x1b']),
    map(char('f'), |_| vec![b'\x0c']),
    map(char('n'), |_| vec![b'\n']),
    map(char('r'), |_| vec![b'\r']),
    map(char('t'), |_| vec![b'\t']),
    map(char('v'), |_| vec![b'\x0b']),
    map(one_of(r#"\'"?"#), |c| vec![c as u8]),
    map(
      fold_many_m_n(
        1,
        3,
        map_opt(verify(anychar, |c| is_oct_digit(*c as u8)), |c| c.to_digit(8).map(|n| n as u8)),
        || 0,
        |acc, n| acc * 8 + n,
      ),
      |n| vec![n],
    ),
    preceded(
      tag_no_case("x"),
      map(
        fold_many_m_n(
          2,
          2,
          map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(8).map(|n| n as u8)),
          || 0,
          |acc, n| acc * 16 + n,
        ),
        |n| vec![n],
      ),
    ),
    preceded(
      char('u'),
      map(
        fold_many_m_n(
          4,
          4,
          map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(8).map(|n| n as u16)),
          || 0,
          |acc, n| acc * 16 + n,
        ),
        |n| n.to_ne_bytes().to_vec(),
      ),
    ),
    preceded(
      char('U'),
      map(
        fold_many_m_n(
          8,
          8,
          map_opt(verify(anychar, |c| is_hex_digit(*c as u8)), |c| c.to_digit(8).map(|n| n as u32)),
          || 0,
          |acc, n| acc * 16 + n,
        ),
        |n| n.to_ne_bytes().to_vec(),
      ),
    ),
  ))(input)
}

/// A character literal.
///
/// ```c
/// #define CHAR 'a'
/// #define CHAR u8'a'
/// #define CHAR u'猫'
/// #define CHAR U'🍌'
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitChar {
  repr: Vec<u8>,
}

impl LitChar {
  pub fn parse<'i, 't, I>(input: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str> + 't,
    <I as InputIter>::Item: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (_, token) = take_one(input)?;

    let (_, c) = all_consuming(delimited(
      preceded(opt(alt((char('L'), terminated(char('u'), char('8')), char('U')))), char('\'')),
      fold_many1(
        alt((preceded(char('\\'), escaped_char), map(none_of(r#"\'"#), |b| vec![b.as_char() as u8]))),
        Vec::new,
        |mut acc, c| {
          acc.clear();
          acc.extend(c);
          acc
        },
      ),
      char('\''),
    ))(token)
    .map_err(|err| err.map_input(|_| input))?;

    Ok((input, Self { repr: c }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    tokens.append_all(match *self.repr.as_slice() {
      [c] => {
        let prefix = &ctx.ffi_prefix();
        let c = proc_macro2::Literal::u8_unsuffixed(c);
        quote! { #c as #prefix c_char }
      },
      [c1, c2] => {
        let c = u16::from_be_bytes([c1, c2]);
        let c = proc_macro2::Literal::u16_unsuffixed(c);
        quote! { #c as wchar_t }
      },
      [c1, c2, c3, c4] => {
        let c = u32::from_be_bytes([c1, c2, c3, c4]);
        let c = proc_macro2::Literal::u32_unsuffixed(c);
        quote! { #c as wchar_t }
      },
      _ => unreachable!(),
    })
  }
}

/// A string literal.
///
/// ```c
/// #define STRING "abc"
/// #define STRING L"def"
/// #define STRING u8"ghi"
/// #define STRING u"jkl"
/// #define STRING U"mno"
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitString {
  pub(crate) repr: Vec<u8>,
}

impl LitString {
  fn parse_inner<'i, 't, I, C>(input: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputTake
      + InputLength
      + Slice<RangeFrom<usize>>
      + InputIter<Item = C>
      + Clone
      + InputTakeAtPosition<Item = C>
      + Compare<&'static str>,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputTakeAtPosition>::Item>,
  {
    let (input2, token) = take_one(input)?;

    let res: IResult<I, Vec<u8>> = all_consuming(delimited(
      preceded(opt(alt((char('L'), terminated(char('u'), char('8')), char('U')))), char('\"')),
      fold_many0(
        alt((
          preceded(char('\\'), escaped_char),
          map(is_not(r#"\""#), |b: I| b.iter_elements().map(|c| c.as_char() as u8).collect()),
        )),
        Vec::new,
        |mut acc, c| {
          acc.extend(c);
          acc
        },
      ),
      char('\"'),
    ))(token);

    if let Ok((_, s)) = res {
      return Ok((input2, Self { repr: s }))
    }

    Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))
  }

  pub fn parse<'i, 't, I, C>(input: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputTake
      + InputLength
      + Slice<RangeFrom<usize>>
      + InputIter<Item = C>
      + Clone
      + InputTakeAtPosition<Item = C>
      + Compare<&'static str>,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputTakeAtPosition>::Item>,
  {
    let (input, s) = Self::parse_inner(input)?;

    fold_many0(
      Self::parse_inner,
      move || s.clone(),
      |mut acc, s| {
        acc.repr.extend(s.repr);
        acc
      },
    )(input)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    let mut bytes = self.repr.clone();
    bytes.push(0);

    let bytes = bytes.into_iter().map(proc_macro2::Literal::u8_unsuffixed);

    let prefix = ctx.ffi_prefix();
    tokens.append_all(quote! {
      [#(#bytes),*].as_ptr() as *const #prefix c_char
    })
  }
}

impl PartialEq<&str> for LitString {
  fn eq(&self, other: &&str) -> bool {
    self.repr == other.as_bytes()
  }
}

/// A floating-point literal.
///
/// ```c
/// #define FLOAT 3.14
/// #define FLOAT 314f
/// #define FLOAT 3.14L
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LitFloat {
  Float(f32),
  Double(f64),
  LongDouble(f64),
}

impl Eq for LitFloat {}

impl LitFloat {
  fn from_str(input: &[u8]) -> IResult<&[u8], (&str, Option<&str>)> {
    all_consuming(map(
      pair(
        map_res(
          recognize(separated_pair(
            opt(digit1),
            alt((value((), char('.')), value((), pair(tag_no_case("e"), opt(alt((char('+'), char('-')))))))),
            digit1,
          )),
          str::from_utf8,
        ),
        opt(map_res(alt((tag_no_case("f"), tag_no_case("l"))), str::from_utf8)),
      ),
      |(f, suffix): (&str, Option<&str>)| (f, suffix),
    ))(input)
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t [u8]]) -> IResult<&'i [&'t [u8]], Self> {
    let (_, input) = take_one(tokens)?;

    let (_, (repr, size1)) = Self::from_str(input).map_err(|err| err.map_input(|_| tokens))?;

    let tokens = &tokens[1..];

    let suffix_f = alt((token("f"), token("F")));
    let suffix_long = alt((token("l"), token("L")));

    let mut suffix = map(
      alt((
        cond(size1.is_none(), opt(preceded(delimited(meta, token("##"), meta), suffix_f))),
        cond(size1.is_none() && repr.contains('.'), opt(preceded(delimited(meta, token("##"), meta), suffix_long))),
      )),
      |size| size.flatten(),
    );

    let (tokens, size2) = suffix(tokens)?;
    let size = size1.or(size2);

    let lit = match size {
      Some("f" | "F") => repr.parse().map(Self::Float),
      Some("l" | "L") => repr.parse().map(Self::LongDouble),
      _ => repr.parse().map(Self::Double),
    };

    if let Ok(lit) = lit {
      return Ok((tokens, lit))
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    let num_prefix = &ctx.num_prefix();

    tokens.append_all(match self {
      Self::Float(f) => match f.classify() {
        FpCategory::Nan => quote! { #num_prefix f32::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #num_prefix f32::INFINITY }
          } else {
            quote! { #num_prefix f32::NEG_INFINITY }
          }
        },
        FpCategory::Zero | FpCategory::Subnormal | FpCategory::Normal => {
          proc_macro2::Literal::f32_unsuffixed(f).to_token_stream()
        },
      },
      Self::Double(f) | Self::LongDouble(f) => match f.classify() {
        FpCategory::Nan => quote! { #num_prefix f64::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #num_prefix f64::INFINITY }
          } else {
            quote! { #num_prefix f64::NEG_INFINITY }
          }
        },
        FpCategory::Zero | FpCategory::Subnormal | FpCategory::Normal => {
          proc_macro2::Literal::f64_unsuffixed(f).to_token_stream()
        },
      },
    })
  }
}

impl Add for LitFloat {
  type Output = Self;

  fn add(self, other: Self) -> Self::Output {
    use LitFloat::*;

    match (self, other) {
      (Float(f1), Float(f2)) => Float(f1 + f2),
      (Float(f1), Double(f2) | LongDouble(f2)) => Double(f1 as f64 + f2),
      (Double(f1) | LongDouble(f1), Float(f2)) => Double(f1 + f2 as f64),
      (Double(f1) | LongDouble(f1), Double(f2) | LongDouble(f2)) => Double(f1 + f2),
    }
  }
}

impl Sub for LitFloat {
  type Output = Self;

  fn sub(self, other: Self) -> Self::Output {
    use LitFloat::*;

    match (self, other) {
      (Float(f1), Float(f2)) => Float(f1 - f2),
      (Float(f1), Double(f2) | LongDouble(f2)) => Double(f1 as f64 - f2),
      (Double(f1) | LongDouble(f1), Float(f2)) => Double(f1 - f2 as f64),
      (Double(f1) | LongDouble(f1), Double(f2) | LongDouble(f2)) => Double(f1 - f2),
    }
  }
}

impl Mul for LitFloat {
  type Output = Self;

  fn mul(self, other: Self) -> Self::Output {
    use LitFloat::*;

    match (self, other) {
      (Float(f1), Float(f2)) => Float(f1 * f2),
      (Float(f1), Double(f2) | LongDouble(f2)) => Double(f1 as f64 * f2),
      (Double(f1) | LongDouble(f1), Float(f2)) => Double(f1 * f2 as f64),
      (Double(f1) | LongDouble(f1), Double(f2) | LongDouble(f2)) => Double(f1 * f2),
    }
  }
}

impl Div for LitFloat {
  type Output = Self;

  fn div(self, other: Self) -> Self::Output {
    use LitFloat::*;

    match (self, other) {
      (Float(f1), Float(f2)) => Float(f1 / f2),
      (Float(f1), Double(f2) | LongDouble(f2)) => Double(f1 as f64 / f2),
      (Double(f1) | LongDouble(f1), Float(f2)) => Double(f1 / f2 as f64),
      (Double(f1) | LongDouble(f1), Double(f2) | LongDouble(f2)) => Double(f1 / f2),
    }
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
  pub value: i128,
  pub suffix: Option<BuiltInType>,
}

impl LitInt {
  fn from_str(input: &[u8]) -> IResult<&[u8], (i128, Option<&str>, Option<&str>)> {
    let digits = alt((
      map_res(preceded(tag_no_case("0x"), hex_digit1), |s| i128::from_str_radix(str::from_utf8(s).unwrap(), 16)),
      map_res(preceded(tag_no_case("0b"), is_a("01")), |s| i128::from_str_radix(str::from_utf8(s).unwrap(), 2)),
      map_res(preceded(tag("0"), oct_digit1), |s| i128::from_str_radix(str::from_utf8(s).unwrap(), 8)),
      map_res(digit1, |s| str::from_utf8(s).unwrap().parse()),
    ));

    let suffix = alt((
      map(
        pair(
          map_res(tag_no_case("u"), str::from_utf8),
          opt(map_res(alt((tag_no_case("ll"), tag_no_case("l"), tag_no_case("z"))), str::from_utf8)),
        ),
        |(unsigned, size)| (Some(unsigned), size),
      ),
      map(
        pair(
          map_res(alt((tag_no_case("ll"), tag_no_case("l"), tag_no_case("z"))), str::from_utf8),
          opt(map_res(tag_no_case("u"), str::from_utf8)),
        ),
        |(size, unsigned)| (unsigned, Some(size)),
      ),
      map(eof, |_| (None, None)),
    ));

    let (input, (n, (unsigned, size))) = all_consuming(pair(digits, suffix))(input)?;
    Ok((input, (n, unsigned, size)))
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t [u8]]) -> IResult<&'i [&'t [u8]], Self> {
    let (_, input) = take_one(tokens)?;

    let (_, (value, unsigned1, size1)) = Self::from_str(input).map_err(|err| err.map_input(|_| tokens))?;

    let suffix_unsigned = alt((token("u"), token("U")));
    let suffix_long = alt((token("l"), token("L")));
    let suffix_long_long = alt((token("ll"), token("LL")));
    let suffix_size_t = alt((token("z"), token("Z")));

    let mut suffix = map(
      permutation((
        cond(unsigned1.is_none(), opt(preceded(delimited(meta, token("##"), meta), suffix_unsigned))),
        cond(
          size1.is_none(),
          opt(preceded(delimited(meta, token("##"), meta), alt((suffix_long_long, suffix_long, suffix_size_t)))),
        ),
      )),
      |(unsigned, size)| (unsigned.flatten(), size.flatten()),
    );

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
    return Ok((tokens, Self { value, suffix }))
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_char() {
    let (_, id) = LitChar::parse(&[r#"'a'"#]).unwrap();
    assert_eq!(id, LitChar { repr: vec![b'a'] });

    let (_, id) = LitChar::parse(&[r#"'abc'"#]).unwrap();
    assert_eq!(id, LitChar { repr: vec![b'c'] });

    let (_, id) = LitChar::parse(&[r#"'\n'"#]).unwrap();
    assert_eq!(id, LitChar { repr: vec![b'\n'] });

    let (_, id) = LitChar::parse(&[r#"'\uFFee'"#]).unwrap();
    assert_eq!(id, LitChar { repr: vec![0xff, 0xee] });

    let (_, id) = LitChar::parse(&[r#"'\UCAFEbabe'"#]).unwrap();
    assert_eq!(id, LitChar { repr: vec![0xca, 0xfe, 0xba, 0xbe] });
  }

  #[test]
  fn parse_string() {
    let (_, id) = LitString::parse(&[r#""asdf""#]).unwrap();
    assert_eq!(id, LitString { repr: "asdf".into() });

    let (_, id) = LitString::parse(&[r#""abc\ndef""#]).unwrap();
    assert_eq!(id, LitString { repr: "abc\ndef".into() });
  }

  #[test]
  fn parse_float() {
    let (_, id) = LitFloat::parse(&[r#"12.34"#]).unwrap();
    assert_eq!(id, LitFloat::Double(12.34));

    let (_, id) = LitFloat::parse(&[r#"12.34f"#]).unwrap();
    assert_eq!(id, LitFloat::Float(12.34));

    let (_, id) = LitFloat::parse(&[r#"12.34L"#]).unwrap();
    assert_eq!(id, LitFloat::LongDouble(12.34));
  }

  #[test]
  fn parse_int() {
    let (_, id) = LitInt::parse(&[r#"777"#]).unwrap();
    assert_eq!(id, LitInt { value: 777, suffix: None });

    let (_, id) = LitInt::parse(&[r#"0777"#]).unwrap();
    assert_eq!(id, LitInt { value: 0o777, suffix: None });

    let (_, id) = LitInt::parse(&[r#"8718937817238719"#]).unwrap();
    assert_eq!(id, LitInt { value: 8718937817238719, suffix: None });

    let (_, id) = LitInt::parse(&[r#"1U"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::UInt) });

    let (_, id) = LitInt::parse(&[r#"1ULL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1UL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULong) });

    let (_, id) = LitInt::parse(&[r#"1LLU"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1z"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: None });
  }
}
