use std::{
  fmt::Debug,
  ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, RangeFrom, RangeTo, Rem, Shl, Shr, Sub},
  str,
};

use nom::{
  branch::alt,
  bytes::complete::{is_a, is_not, tag, tag_no_case},
  character::{
    complete::{anychar, char, digit1, hex_digit1, none_of, oct_digit1, one_of},
    is_hex_digit, is_oct_digit,
  },
  combinator::{all_consuming, cond, eof, map, map_opt, map_parser, map_res, opt, recognize, success, value, verify},
  multi::{fold_many0, fold_many_m_n, many0, many1},
  sequence::{delimited, pair, preceded, terminated, tuple},
  AsBytes, AsChar, Compare, CompareResult, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake,
  InputTakeAtPosition, Offset, ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
use std::num::FpCategory;

use super::{
  tokens::{meta, take_one, token},
  ty::BuiltInType,
};
use crate::{CodegenContext, Identifier, LitIdent, LocalContext, Type};

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

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
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

fn simple_escape_sequence<I>(input: I) -> IResult<I, u32>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + InputIter + Clone + Compare<&'static str>,
  <I as InputIter>::Item: AsChar + Copy,
  &'static str: FindToken<<I as InputIter>::Item>,
{
  alt((
    map(char('a'), |_| '\x07' as u32),
    map(char('b'), |_| '\x08' as u32),
    map(char('e'), |_| '\x1b' as u32),
    map(char('f'), |_| '\x0c' as u32),
    map(char('n'), |_| '\n' as u32),
    map(char('r'), |_| '\r' as u32),
    map(char('t'), |_| '\t' as u32),
    map(char('v'), |_| '\x0b' as u32),
    map(one_of(r#"\'"?"#), |c| c as u32),
  ))(input)
}

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
  preceded(char('\\'), alt((simple_escape_sequence, numeric_escape_sequence, universal_char)))(input)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LitCharPrefix {
  Utf8,
  Utf16,
  Utf32,
  Wide,
}

/// A character literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LitChar {
  /// An ordinary character (`char`) literal.
  ///
  /// ```c
  /// #define CHAR 'a'
  /// ```
  Ordinary(u8),
  /// A UTF-8 character (`char8_t`) literal.
  ///
  /// ```c
  /// #define CHAR u8'a'
  /// ```
  Utf8(u8),
  /// A UTF-16 character (`char16_t`) literal.
  ///
  /// ```c
  /// #define CHAR u'猫'
  /// ```
  Utf16(u16),
  /// A UTF-32 character (`char32_t`) literal.
  ///
  /// ```c
  /// #define CHAR U'🍌'
  /// ```
  Utf32(u32),
  /// A wide character (`wchar_t`) literal.
  ///
  /// ```c
  /// #define CHAR L'β'
  /// ```
  Wide(u32),
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

    let one_char = |input| alt((escaped_char, map(none_of("\\\'\n"), |b| u32::from(b.as_char()))))(input);

    let parse_char = |(prefix, c)| match prefix {
      None if c <= 0xff => Some(LitChar::Ordinary(c as u8)),
      Some(LitCharPrefix::Utf8) if c <= 0x7f => Some(LitChar::Utf8(c as u8)),
      Some(LitCharPrefix::Utf16) if c <= u16::MAX as u32 => Some(LitChar::Utf16(c as u16)),
      Some(LitCharPrefix::Utf32) => Some(LitChar::Utf32(c)),
      Some(LitCharPrefix::Wide) => Some(LitChar::Wide(c)),
      _ => None,
    };

    let (_, c) = all_consuming(terminated(
      alt((
        map_opt(
          cond(utf8_prefix, map(preceded(char('\''), one_char), |c| parse_char((Some(LitCharPrefix::Utf8), c)))),
          |c| c.flatten(),
        ),
        preceded(char('\''), map_opt(one_char, |c| parse_char((None, c)))),
        map_opt(
          pair(
            terminated(
              opt(alt((
                value(LitCharPrefix::Utf8, tag("u8")),
                value(LitCharPrefix::Utf16, tag("u")),
                value(LitCharPrefix::Utf32, tag("U")),
                value(LitCharPrefix::Wide, tag("L")),
              ))),
              char('\''),
            ),
            one_char,
          ),
          parse_char,
        ),
      )),
      char('\''),
    ))(token)
    .map_err(|err| err.map_input(|_| input))?;

    Ok((input2, c))
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    Ok(match self {
      LitChar::Ordinary(_) => Some(Type::BuiltIn(BuiltInType::Char)),
      LitChar::Utf8(_) => Some(Type::BuiltIn(BuiltInType::Char8T)),
      LitChar::Utf16(_) => Some(Type::BuiltIn(BuiltInType::Char16T)),
      LitChar::Utf32(_) => Some(Type::BuiltIn(BuiltInType::Char32T)),
      LitChar::Wide(_) => {
        let mut ty = Type::Identifier {
          name: Identifier::Literal(LitIdent { id: "wchar_t".to_owned(), macro_arg: false }),
          is_struct: false,
        };
        ty.finish(ctx)?;
        Some(ty)
      },
    })
  }

  #[allow(unused_variables)]
  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let c = match *self {
      Self::Ordinary(c) => {
        if let Some(c) = char::from_u32(c as u32) {
          proc_macro2::Literal::character(c)
        } else {
          proc_macro2::Literal::u8_suffixed(c)
        }
      },
      Self::Utf8(c) => {
        if let Some(c) = char::from_u32(c as u32) {
          proc_macro2::Literal::character(c)
        } else {
          proc_macro2::Literal::u8_suffixed(c)
        }
      },
      Self::Utf16(c) => {
        if let Some(c) = char::from_u32(c as u32) {
          proc_macro2::Literal::character(c)
        } else {
          proc_macro2::Literal::u16_suffixed(c)
        }
      },
      Self::Utf32(c) => {
        if let Some(c) = char::from_u32(c) {
          proc_macro2::Literal::character(c)
        } else {
          proc_macro2::Literal::u32_suffixed(c)
        }
      },
      Self::Wide(c) => {
        if let Some(c) = char::from_u32(c) {
          proc_macro2::Literal::character(c)
        } else {
          proc_macro2::Literal::u32_suffixed(c)
        }
      },
    };

    // Output only the character itself, the type is added
    // by converting this to a cast in `Expr::finish`.
    tokens.append_all(quote! { #c });
  }
}

/// A string literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LitString {
  /// An ordinary string (`const char*`) literal.
  ///
  /// ```c
  /// #define STRING "abc"
  /// ```
  Ordinary(Vec<u8>),
  /// A UTF-8 string (`const char8_t*`) literal.
  ///
  /// ```c
  /// #define STRING u8"def"
  /// ```
  Utf8(String),
  /// A UTF-16 string (`const char16_t*`) literal.
  ///
  /// ```c
  /// #define STRING u"ghi"
  /// ```
  Utf16(String),
  /// A UTF-32 string (`const char32_t*`) literal.
  ///
  /// ```c
  /// #define STRING U"jkl"
  /// ```
  Utf32(String),
  /// A wide string (`const wchar_t*`) literal.
  ///
  /// ```c
  /// #define STRING L"mno"
  /// ```
  Wide(Vec<u32>),
}

impl LitString {
  fn parse_ordinary<I, C>(input: I) -> IResult<I, Vec<u8>>
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
    delimited(
      char('\"'),
      fold_many0(
        alt((
          map_opt(escaped_char, |c| if c <= 0xff { Some(vec![c as u8]) } else { None }),
          map(is_not("\\\"\n"), |b: I| {
            let s: String = b.iter_elements().map(|c| c.as_char()).collect();
            s.into_bytes()
          }),
        )),
        Vec::new,
        |mut acc, c| {
          acc.extend(c);
          acc
        },
      ),
      char('\"'),
    )(input)
  }

  fn parse_utf8<I, C>(input: I) -> IResult<I, String>
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
    map_res(
      delimited(
        char('\"'),
        fold_many0(
          alt((
            many1(map_res(escaped_char, u8::try_from)),
            map(is_not("\\\"\n"), |b: I| {
              let s: String = b.iter_elements().map(|c| c.as_char()).collect();
              s.into_bytes()
            }),
          )),
          Vec::new,
          |mut acc, c| {
            acc.extend(c);
            acc
          },
        ),
        char('\"'),
      ),
      String::from_utf8,
    )(input)
  }

  fn parse_utf16<I, C>(input: I) -> IResult<I, String>
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
    map_res(
      delimited(
        char('\"'),
        fold_many0(
          alt((
            many1(map_res(escaped_char, u16::try_from)),
            map(is_not("\\\"\n"), |b: I| {
              let s: String = b.iter_elements().map(|c| c.as_char()).collect();
              s.encode_utf16().collect()
            }),
          )),
          Vec::new,
          |mut acc, c| {
            acc.extend(c);
            acc
          },
        ),
        char('\"'),
      ),
      |v| String::from_utf16(&v),
    )(input)
  }

  fn parse_utf32<I, C>(input: I) -> IResult<I, String>
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
    map_opt(delimited(char('\"'), many0(alt((escaped_char, map(none_of("\\\"\n"), u32::from)))), char('\"')), |chars| {
      chars.into_iter().map(char::from_u32).collect::<Option<String>>()
    })(input)
  }

  fn parse_wide<I, C>(input: I) -> IResult<I, Vec<u32>>
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
    delimited(char('\"'), many0(alt((escaped_char, map(none_of("\\\"\n"), u32::from)))), char('\"'))(input)
  }

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

    let res: IResult<I, Self> = all_consuming(alt((
      map(Self::parse_ordinary, Self::Ordinary),
      preceded(tag("u8"), map(Self::parse_utf8, Self::Utf8)),
      preceded(tag("u"), map(Self::parse_utf16, Self::Utf16)),
      preceded(tag("U"), map(Self::parse_utf32, Self::Utf32)),
      preceded(tag("L"), map(Self::parse_wide, Self::Wide)),
    )))(token);

    if let Ok((_, s)) = res {
      return Ok((input2, s))
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

    match s {
      Self::Ordinary(bytes) => map(
        fold_many0(
          map_parser(take_one, |token| {
            all_consuming(Self::parse_ordinary)(token)
              .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| input))
          }),
          move || bytes.clone(),
          |mut acc, s| {
            acc.extend(s);
            acc
          },
        ),
        Self::Ordinary,
      )(input),
      Self::Utf8(s) => map(
        fold_many0(
          map_parser(take_one, |token| {
            all_consuming(Self::parse_utf8)(token)
              .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| input))
          }),
          move || s.clone(),
          |mut acc, s| {
            acc.push_str(&s);
            acc
          },
        ),
        Self::Utf8,
      )(input),
      Self::Utf16(s) => map(
        fold_many0(
          map_parser(take_one, |token| {
            all_consuming(Self::parse_utf16)(token)
              .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| input))
          }),
          move || s.clone(),
          |mut acc, s| {
            acc.push_str(&s);
            acc
          },
        ),
        Self::Utf16,
      )(input),
      Self::Utf32(s) => map(
        fold_many0(
          map_parser(take_one, |token| {
            all_consuming(Self::parse_utf32)(token)
              .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| input))
          }),
          move || s.clone(),
          |mut acc, s| {
            acc.push_str(&s);
            acc
          },
        ),
        Self::Utf32,
      )(input),
      Self::Wide(v) => map(
        fold_many0(
          map_parser(take_one, |token| {
            all_consuming(Self::parse_wide)(token)
              .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| input))
          }),
          move || v.clone(),
          |mut acc, s| {
            acc.extend(s);
            acc
          },
        ),
        Self::Wide,
      )(input),
    }
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    let ty = match self {
      Self::Ordinary(_) => Type::BuiltIn(BuiltInType::Char),
      Self::Utf8(_) => Type::BuiltIn(BuiltInType::Char8T),
      Self::Utf16(_) => Type::BuiltIn(BuiltInType::Char16T),
      Self::Utf32(_) => Type::BuiltIn(BuiltInType::Char32T),
      Self::Wide(_) => {
        let mut ty = Type::Identifier {
          name: Identifier::Literal(LitIdent { id: "wchar_t".to_owned(), macro_arg: false }),
          is_struct: false,
        };
        ty.finish(ctx)?;
        ty
      },
    };

    Ok(Some(Type::Ptr { ty: Box::new(ty), mutable: false }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Ordinary(bytes) => {
        let mut bytes = bytes.clone();
        bytes.push(0);

        let byte_count = proc_macro2::Literal::usize_unsuffixed(bytes.len());
        let byte_string = proc_macro2::Literal::byte_string(&bytes);

        if ctx.is_variable_macro() {
          let ffi_prefix = ctx.trait_prefix().map(|trait_prefix| quote! { #trait_prefix ffi:: });
          tokens.append_all(quote! {
            {
              const BYTES: &[u8; #byte_count] = #byte_string;
              #[allow(unsafe_code)]
              unsafe { #ffi_prefix CStr::from_bytes_with_nul_unchecked(BYTES) }
            }
          })
        } else {
          let ffi_prefix = ctx.ffi_prefix();
          tokens.append_all(quote! {
            {
              const BYTES: &[u8; #byte_count] = #byte_string;
              BYTES.as_ptr() as *const #ffi_prefix c_char
            }
          })
        }
      },
      Self::Utf8(s) => {
        let mut bytes = s.as_bytes().to_vec();
        bytes.push(0);

        let byte_string = proc_macro2::Literal::byte_string(&bytes);
        tokens.append_all(quote! { #byte_string })
      },
      Self::Utf16(s) => {
        let c = s.encode_utf16().chain(std::iter::once(0));
        tokens.append_all(quote! { &[#(#c),*] })
      },
      Self::Utf32(s) => {
        let c = s.chars().map(u32::from).chain(std::iter::once(0));
        tokens.append_all(quote! { &[#(#c),*] })
      },
      Self::Wide(s) => {
        let s = s.iter().cloned().chain(std::iter::once(0)).map(proc_macro2::Literal::u32_unsuffixed);
        tokens.append_all(quote! { &[#(#s),*] })
      },
    }
  }

  /// Get the raw string representation as bytes.
  pub(crate) fn as_bytes(&self) -> Option<&[u8]> {
    match self {
      Self::Ordinary(bytes) => Some(bytes.as_slice()),
      Self::Utf8(s) => Some(s.as_bytes()),
      Self::Utf16(s) => Some(s.as_bytes()),
      Self::Utf32(s) => Some(s.as_bytes()),
      Self::Wide(_) => None,
    }
  }
}

impl PartialEq<&str> for LitString {
  fn eq(&self, other: &&str) -> bool {
    self.as_bytes() == Some(other.as_bytes())
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
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
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
              map_parser(take_one, |token| {
                Self::parse_suffix(token).map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
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
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
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
    assert_eq!(id, LitChar::Ordinary('a' as u8));
    assert!(rest.is_empty());

    let (_, id) = LitChar::parse(&[r#"'\n'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary('\n' as u8));

    let (_, id) = LitChar::parse(&[r#"'\''"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary('\'' as u8));

    let (_, id) = LitChar::parse(&[r#"u'\uFFee'"#]).unwrap();
    assert_eq!(id, LitChar::Utf16(0xffee));

    let (_, id) = LitChar::parse(&[r#"U'\U0001f369'"#]).unwrap();
    assert_eq!(id, LitChar::Utf32(0x0001f369));

    let (_, id) = LitChar::parse(&[r#"U'🍌'"#]).unwrap();
    assert_eq!(id, LitChar::Utf32(0x0001f34c));

    let (_, id) = LitChar::parse(&[r#"'\xff'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(0xff));

    let (_, id) = LitChar::parse(&[r#"'ÿ'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(0xff));
  }

  #[test]
  fn parse_string() {
    let (_, id) = LitString::parse(&[r#""asdf""#]).unwrap();
    assert_eq!(id, LitString::Ordinary("asdf".into()));

    let (_, id) = LitString::parse(&[r#""\360\237\216\247🎧""#]).unwrap();
    assert_eq!(id, LitString::Ordinary("🎧🎧".into()));

    let (_, id) = LitString::parse(&[r#""abc\ndef""#]).unwrap();
    assert_eq!(id, LitString::Ordinary("abc\ndef".into()));

    let (_, id) = LitString::parse(&[r#""escaped\"quote""#]).unwrap();
    assert_eq!(id, LitString::Ordinary(r#"escaped"quote"#.into()));

    let (_, id) = LitString::parse(&[r#"u8"🎧\xf0\x9f\x8e\xa4""#]).unwrap();
    assert_eq!(id, LitString::Utf8("🎧🎤".into()));

    let (_, id) = LitString::parse(&[r#"u8"Put your 🎧 on.""#]).unwrap();
    assert_eq!(id, LitString::Utf8("Put your 🎧 on.".into()));

    let (_, id) = LitString::parse(&[r#"u"🎧\uD83C\uDFA4""#]).unwrap();
    assert_eq!(id, LitString::Utf16("🎧🎤".into()));

    let (_, id) = LitString::parse(&[r#"U"🎧\U0001F3A4""#]).unwrap();
    assert_eq!(id, LitString::Utf32("🎧🎤".into()));
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
  fn parse_int_llu() {
    let (_, id) = LitInt::parse(&["1", "##", "LL", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });
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

    let (_, id) = LitInt::parse(&["1", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::UInt) });

    let (_, id) = LitInt::parse(&[r#"3L"#]).unwrap();
    assert_eq!(id, LitInt { value: 3, suffix: Some(BuiltInType::Long) });

    let (_, id) = LitInt::parse(&[r#"1ULL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&["1", "##", "U", "##", "LL"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&["1", "##", "ULL"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1UL"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULong) });

    let (_, id) = LitInt::parse(&[r#"1LLU"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&["1", "##", "LL", "##", "U"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&["1", "##", "LLU"]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: Some(BuiltInType::ULongLong) });

    let (_, id) = LitInt::parse(&[r#"1z"#]).unwrap();
    assert_eq!(id, LitInt { value: 1, suffix: None });

    let (_, id) = LitInt::parse(&["1", "##", "z"]).unwrap();
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
