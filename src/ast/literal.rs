use std::{
  fmt::Debug,
  ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, RangeFrom, RangeTo, Rem, Shl, Shr, Sub},
  str,
};

use nom::{
  branch::{alt, permutation},
  bytes::complete::{is_a, is_not, tag, tag_no_case},
  character::{
    complete::{anychar, char, digit1, hex_digit1, none_of, oct_digit1, one_of},
    is_hex_digit, is_oct_digit,
  },
  combinator::{all_consuming, cond, eof, map, map_opt, opt, recognize, value, verify},
  multi::{fold_many0, fold_many1, fold_many_m_n},
  sequence::{delimited, pair, preceded, terminated, tuple},
  AsBytes, AsChar, Compare, FindSubstring,
};

use nom::{
  CompareResult, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset, ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
use std::num::FpCategory;

use super::{
  tokens::{meta, take_one, token},
  ty::BuiltInType,
};
use crate::{CodegenContext, LocalContext, Type};

/// A literal.
///
/// Also see [`LitChar`], [`LitString`], [`LitFloat`] and [`LitInt`].
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

impl From<char> for Lit {
  fn from(c: char) -> Lit {
    Lit::Char(LitChar { repr: c as u32 })
  }
}

impl From<i32> for Lit {
  fn from(n: i32) -> Lit {
    Lit::Int(LitInt { value: n.into(), suffix: None })
  }
}

impl Lit {
  /// Parse a literal.
  pub fn parse<I, C>(input: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + InputIter<Item = C>
      + Clone
      + InputTakeAtPosition<Item = C>
      + Compare<&'static str>
      + Offset
      + ParseTo<f32>
      + ParseTo<f64>
      + FindSubstring<&'static str>,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    alt((
      map(LitChar::parse, Self::Char),
      map(LitString::parse, Self::String),
      map(LitFloat::parse, Self::Float),
      map(LitInt::parse, Self::Int),
    ))(input)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
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
  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Char(c) => c.to_tokens(ctx, tokens),
      Self::String(s) => s.to_tokens(ctx, tokens),
      Self::Float(f) => f.to_tokens(ctx, tokens),
      Self::Int(i) => i.to_tokens(ctx, tokens),
    }
  }
}

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

fn escaped_char<I>(input: I) -> IResult<I, u32>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  alt((
    map(char('a'), |_| b'\x07' as u32),
    map(char('b'), |_| b'\x08' as u32),
    map(char('e'), |_| b'\x1b' as u32),
    map(char('f'), |_| b'\x0c' as u32),
    map(char('n'), |_| b'\n' as u32),
    map(char('r'), |_| b'\r' as u32),
    map(char('t'), |_| b'\t' as u32),
    map(char('v'), |_| b'\x0b' as u32),
    map(one_of(r#"\'"?"#), |c| c as u32),
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
    universal_char,
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
  pub(crate) repr: u32,
}

impl LitChar {
  /// Parse a character literal.
  pub fn parse<I>(input: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Offset
      + InputIter
      + Clone
      + Compare<&'static str>,
    <I as InputIter>::Item: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (input, utf8_prefix) = if let Ok((input, _)) = token("u8")(input) { (input, true) } else { (input, false) };
    let (input2, token) = take_one(input)?;

    let fold_char = |input| {
      fold_many1(
        alt((preceded(char('\\'), escaped_char), map(none_of("\\\'\n"), |b| b.as_char() as u32))),
        || 0,
        |acc, c| {
          if c <= u8::MAX as u32 {
            acc << 8 | c
          } else if c <= u16::MAX as u32 {
            acc << 16 | c
          } else {
            c
          }
        },
      )(input)
    };

    let parse_char = |(prefix, c)| {
      let max = match prefix {
        Some("u8") => 0x7f,
        Some("u") => 0xffff,
        Some("U") | Some("L") => u32::MAX,
        _ => 0xff,
      };

      if c <= max {
        let c = if let Some(c) = char::from_u32(c) {
          c as u32
        } else {
          let b = c.to_be_bytes();
          if let Some(c) = str::from_utf8(&b).ok().and_then(|s| s.chars().last()) {
            c as u32
          } else {
            c
          }
        };

        Some(c)
      } else {
        None
      }
    };

    let (_, c) = all_consuming(terminated(
      alt((
        map_opt(cond(utf8_prefix, map(preceded(char('\''), fold_char), |c| parse_char((Some("u8"), c)))), |c| {
          c.flatten()
        }),
        preceded(
          char('\''),
          map_opt(
            fold_many1(
              alt((preceded(char('\\'), escaped_char), map(none_of("\\\'\n"), |b| b.as_char() as u32))),
              || 0u32,
              |_, c| c,
            ),
            |c| if c <= 0xff { Some(c) } else { None },
          ),
        ),
        map_opt(
          pair(
            terminated(
              opt(alt((value("u8", tag("u8")), value("u", tag("u")), value("U", tag("U")), value("L", tag("L"))))),
              char('\''),
            ),
            fold_char,
          ),
          parse_char,
        ),
      )),
      char('\''),
    ))(token)
    .map_err(|err| err.map_input(|_| input))?;

    Ok((input2, Self { repr: c }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    if self.repr <= u8::MAX as u32 {
      Ok(Some(Type::BuiltIn(BuiltInType::Char)))
    } else {
      Ok(None)
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let c = self.repr;

    tokens.append_all(if c <= u8::MAX as u32 {
      let ffi_prefix = &ctx.ffi_prefix();
      let c = match char::from_u32(c) {
        Some(c) => proc_macro2::Literal::character(c),
        None => proc_macro2::Literal::u8_suffixed(c as u8),
      };
      quote! { #c as #ffi_prefix c_char }
    } else if c <= u16::MAX as u32 {
      let c = match char::from_u32(c) {
        Some(c) => proc_macro2::Literal::character(c),
        None => proc_macro2::Literal::u16_suffixed(c as u16),
      };
      quote! { #c as char16_t }
    } else {
      let c = match char::from_u32(c) {
        Some(c) => proc_macro2::Literal::character(c),
        None => proc_macro2::Literal::u32_suffixed(c),
      };
      quote! { #c as char32_t }
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
  fn parse_inner<I, C>(input: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
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

    let res: IResult<I, Vec<u8>> = all_consuming(map_opt(
      pair(
        opt(alt((value("u8", tag("u8")), value("u", tag("u")), value("U", tag("U")), value("L", tag("L"))))),
        delimited(
          char('\"'),
          fold_many0(
            alt((
              fold_many1(preceded(char('\\'), escaped_char), Vec::new, |mut acc, c| {
                acc.push(c);
                acc
              }),
              map(is_not("\\\"\n"), |b: I| b.iter_elements().map(|c| c.as_char() as u32).collect()),
            )),
            Vec::new,
            |mut acc, c| {
              acc.extend(c);
              acc
            },
          ),
          char('\"'),
        ),
      ),
      |(prefix, s)| {
        match prefix {
          Some("u8") | Some("u") | Some("U") => {
            if prefix == Some("u8") {
              let s_utf8: Option<Vec<u8>> = s.iter().map(|c| if *c <= 0xff { Some(*c as u8) } else { None }).collect();
              if let Some(s) = s_utf8.and_then(|s| String::from_utf8(s).ok()) {
                return Some(s.into())
              }
            }

            if prefix == Some("u") {
              let s_utf8: Option<Vec<u16>> =
                s.iter().map(|c| if *c <= 0xffff { Some(*c as u16) } else { None }).collect();
              if let Some(s) = s_utf8.and_then(|s| String::from_utf16(&s).ok()) {
                return Some(s.into())
              }
            }

            let s: Option<String> = s.iter().map(|c| char::from_u32(*c)).collect();
            return Some(s?.into())
          },
          _ => {},
        }

        let mut acc = Vec::new();
        for c in s.into_iter() {
          let c = if c <= u8::MAX as u32 {
            vec![c as u8]
          } else if c <= u16::MAX as u32 {
            (c as u16).to_be_bytes().to_vec()
          } else {
            c.to_be_bytes().to_vec()
          };

          acc.extend(c);
        }

        Some(acc)
      },
    ))(token);

    if let Ok((_, s)) = res {
      return Ok((input2, Self { repr: s }))
    }

    Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))
  }

  /// Parse a string literal.
  pub fn parse<I, C>(input: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
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

  #[allow(unused_variables)]
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let mut bytes = self.repr.clone();
    bytes.push(0);

    let byte_count = proc_macro2::Literal::usize_unsuffixed(bytes.len());
    let byte_string = proc_macro2::Literal::byte_string(&bytes);

    let prefix = ctx.ffi_prefix();
    tokens.append_all(quote! {
      {
        const BYTES: [u8; #byte_count] = *#byte_string;
        BYTES.as_ptr() as *const #prefix c_char
      }
    })
  }

  /// Get the raw string representation as bytes.
  pub fn as_bytes(&self) -> &[u8] {
    &self.repr
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
  /// A `float`.
  Float(f32),
  /// A `double`.
  Double(f64),
  /// A `long double`.
  LongDouble(f64),
}

impl Eq for LitFloat {}

impl LitFloat {
  fn from_str<I, C>(input: I) -> IResult<I, (I, Option<&'static str>)>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<RangeTo<usize>>
      + Slice<RangeFrom<usize>>
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Compare<&'static str>
      + Offset
      + Clone,

    C: AsChar,
  {
    let decimal = |input| recognize(pair(char('.'), digit1))(input);
    let scientific = |input| recognize(tuple((tag_no_case("e"), opt(alt((char('+'), char('-')))), digit1)))(input);

    all_consuming(pair(
      alt((
        recognize(pair(
          alt((
            // 1.1 | .1
            recognize(pair(opt(digit1), decimal)),
            // 1.
            recognize(pair(digit1, char('.'))),
          )),
          opt(scientific),
        )),
        // 1e1
        recognize(pair(digit1, scientific)),
      )),
      opt(alt((map(tag_no_case("f"), |_| "f"), map(tag_no_case("l"), |_| "l")))),
    ))(input)
  }

  /// Parse a floating-point literal.
  pub fn parse<I, C>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<RangeTo<usize>>
      + Slice<RangeFrom<usize>>
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Compare<&'static str>
      + Offset
      + Clone
      + ParseTo<f32>
      + ParseTo<f64>
      + FindSubstring<&'static str>,
    C: AsChar,
  {
    let (_, input) = take_one(tokens)?;

    let (_, (repr, size1)) = Self::from_str(input).map_err(|err| err.map_input(|_| tokens))?;

    let tokens = &tokens[1..];

    let suffix_f = alt((token("f"), token("F")));
    let suffix_long = alt((token("l"), token("L")));

    let mut suffix = map(
      cond(
        size1.is_none(),
        opt(alt((
          preceded(delimited(meta, token("##"), meta), suffix_f),
          preceded(delimited(meta, token("##"), meta), suffix_long),
        ))),
      ),
      |size| size.flatten(),
    );

    let (tokens, size2) = suffix(tokens)?;
    let size = size1.or(size2);

    let lit = match size {
      Some(s) if s.compare_no_case("f") == CompareResult::Ok => repr.parse_to().map(Self::Float),
      Some(s) if s.compare_no_case("l") == CompareResult::Ok => repr.parse_to().map(Self::LongDouble),
      _ => repr.parse_to().map(Self::Double),
    };

    if let Some(lit) = lit {
      return Ok((tokens, lit))
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Float)))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    Ok(Some(match self {
      Self::Float(_) => Type::BuiltIn(BuiltInType::Float),
      Self::Double(_) => Type::BuiltIn(BuiltInType::Double),
      Self::LongDouble(_) => Type::BuiltIn(BuiltInType::LongDouble),
    }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let trait_prefix = &ctx.trait_prefix();

    tokens.append_all(match self {
      Self::Float(f) => match f.classify() {
        FpCategory::Nan => quote! { #trait_prefix f32::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #trait_prefix f32::INFINITY }
          } else {
            quote! { #trait_prefix f32::NEG_INFINITY }
          }
        },
        FpCategory::Zero | FpCategory::Subnormal | FpCategory::Normal => {
          proc_macro2::Literal::f32_unsuffixed(f).to_token_stream()
        },
      },
      Self::Double(f) | Self::LongDouble(f) => match f.classify() {
        FpCategory::Nan => quote! { #trait_prefix f64::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #trait_prefix f64::INFINITY }
          } else {
            quote! { #trait_prefix f64::NEG_INFINITY }
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

    let suffix = alt((
      map(
        pair(
          map(tag_no_case("u"), |_| "u"),
          opt(alt((map(tag_no_case("ll"), |_| "ll"), map(tag_no_case("l"), |_| "l"), map(tag_no_case("z"), |_| "z")))),
        ),
        |(unsigned, size)| (Some(unsigned), size),
      ),
      map(
        pair(
          alt((map(tag_no_case("ll"), |_| "ll"), map(tag_no_case("l"), |_| "l"), map(tag_no_case("z"), |_| "z"))),
          opt(map(tag_no_case("u"), |_| "u")),
        ),
        |(size, unsigned)| (unsigned, Some(size)),
      ),
      map(eof, |_| (None, None)),
    ));

    let (input, (n, (unsigned, size))) = all_consuming(pair(digits, suffix))(input)?;
    Ok((input, (n, unsigned, size)))
  }

  /// Parse an integer literal.
  pub fn parse<I, C>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + Slice<std::ops::RangeFrom<usize>>
      + Compare<&'static str>
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + FindSubstring<&'static str>
      + Clone,
    C: AsChar,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, input) = take_one(tokens)?;

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
    Ok((tokens, Self { value, suffix }))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
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

  #[test]
  fn parse_char() {
    let (rest, id) = LitChar::parse(&[r#"'a'"#]).unwrap();
    assert_eq!(id, LitChar { repr: 'a' as u32 });
    assert!(rest.is_empty());

    let (_, id) = LitChar::parse(&[r#"'abc'"#]).unwrap();
    assert_eq!(id, LitChar { repr: 'c' as u32 });

    let (_, id) = LitChar::parse(&[r#"'\n'"#]).unwrap();
    assert_eq!(id, LitChar { repr: '\n' as u32 });

    let (_, id) = LitChar::parse(&[r#"u'\uFFee'"#]).unwrap();
    assert_eq!(id, LitChar { repr: 0xffee });

    let (_, id) = LitChar::parse(&[r#"U'\U0001f369'"#]).unwrap();
    assert_eq!(id, LitChar { repr: 0x0001f369 });

    let (_, id) = LitChar::parse(&[r#"U'🍌'"#]).unwrap();
    assert_eq!(id, LitChar { repr: 0x0001f34c });

    let c: &[u8] = &[b'U', b'\'', 0x00, 0x01, 0xf3, 0x4c, b'\''];
    let (_, id) = LitChar::parse(&[c]).unwrap();
    assert_eq!(id, LitChar { repr: 0x0001f34c });
  }

  #[test]
  fn parse_string() {
    let (_, id) = LitString::parse(&[r#""asdf""#]).unwrap();
    assert_eq!(id, LitString { repr: "asdf".into() });

    let (_, id) = LitString::parse(&[r#""abc\ndef""#]).unwrap();
    assert_eq!(id, LitString { repr: "abc\ndef".into() });

    let (_, id) = LitString::parse(&[r#""escaped\"quote""#]).unwrap();
    assert_eq!(id, LitString { repr: r#"escaped"quote"#.into() });

    let (_, id) = LitString::parse(&[r#"u8"🎧""#]).unwrap();
    assert_eq!(id, LitString { repr: "🎧".into() });

    let (_, id) = LitString::parse(&[r#"u8"Put your 🎧 on.""#]).unwrap();
    assert_eq!(id, LitString { repr: "Put your 🎧 on.".into() });

    let (_, id) = LitString::parse(&[r#"u8"Put your 🎧 on.""#.as_bytes()]).unwrap();
    assert_eq!(id, LitString { repr: "Put your 🎧 on.".into() });
  }

  #[test]
  fn parse_float() {
    let (_, id) = LitFloat::parse(&[r#"12.34"#]).unwrap();
    assert_eq!(id, LitFloat::Double(12.34));

    let (_, id) = LitFloat::parse(&[r#"12.34f"#]).unwrap();
    assert_eq!(id, LitFloat::Float(12.34));

    let (_, id) = LitFloat::parse(&[r#"12.34L"#]).unwrap();
    assert_eq!(id, LitFloat::LongDouble(12.34));

    let (_, id) = LitFloat::parse(&[r#".1"#]).unwrap();
    assert_eq!(id, LitFloat::Double(0.1));

    let (_, id) = LitFloat::parse(&[r#"1."#]).unwrap();
    assert_eq!(id, LitFloat::Double(1.0));

    let (_, id) = LitFloat::parse(&[r#"1e1"#]).unwrap();
    assert_eq!(id, LitFloat::Double(10.0));

    let (_, id) = LitFloat::parse(&[r#"1e-1f"#]).unwrap();
    assert_eq!(id, LitFloat::Float(0.1));
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

    let (_, id) = LitInt::parse(&[r#"3L"#]).unwrap();
    assert_eq!(id, LitInt { value: 3, suffix: Some(BuiltInType::Long) });

    let (_, id) = LitInt::parse(&[r#"1ULL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1UL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULong) });

    let (_, id) = LitInt::parse(&[r#"1LLU"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1z"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: None });

    let (_, id) = LitInt::parse(&[r#"28Z"#]).unwrap();
    assert_eq!(id, LitInt { value: 28, suffix: None });

    let (_, id) = LitInt::parse(&[r#"0xff"#]).unwrap();
    assert_eq!(id, LitInt { value: 0xff, suffix: None });

    let (_, id) = LitInt::parse(&[r#"0XFF"#]).unwrap();
    assert_eq!(id, LitInt { value: 0xff, suffix: None });

    let (_, id) = LitInt::parse(&[r#"0b101"#]).unwrap();
    assert_eq!(id, LitInt { value: 0b101, suffix: None });

    let (_, id) = LitInt::parse(&[r#"0B1100"#]).unwrap();
    assert_eq!(id, LitInt { value: 0b1100, suffix: None });
  }

  #[test]
  fn rest() {
    let (rest, id) = LitInt::parse(&[r#"0"#]).unwrap();
    assert_eq!(id, LitInt { value: 0, suffix: None });
    assert!(rest.is_empty());
  }
}
