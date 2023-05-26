use std::{fmt::Debug, ops::RangeFrom, str};

use nom::{
  branch::alt,
  bytes::complete::{is_not, tag},
  character::complete::{char, none_of},
  combinator::{all_consuming, map, map_parser, map_res, opt},
  multi::{fold_many0, many0, many1},
  sequence::{delimited, preceded},
  AsChar, Compare, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Slice,
};
use proc_macro2::TokenStream;
use quote::quote;

use crate::{BuiltInType, CodegenContext, Expr, LocalContext, Type};

use super::{escaped_char, take_one, Identifier, LitIdent};

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
  /// Parse
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
    map_res(Self::parse_ordinary, String::from_utf8)(input)
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
    map(
      delimited(char('\"'), many0(alt((map_res(escaped_char, char::try_from), none_of("\\\"\n")))), char('\"')),
      |chars| chars.into_iter().collect::<String>(),
    )(input)
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
            all_consuming(preceded(opt(tag("u8")), Self::parse_utf8))(token)
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
            all_consuming(preceded(opt(tag("u")), Self::parse_utf16))(token)
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
            all_consuming(preceded(opt(tag("U")), Self::parse_utf32))(token)
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
            all_consuming(preceded(opt(tag("L")), Self::parse_wide))(token)
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
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
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
          name: Box::new(Expr::Variable {
            name: Identifier::Literal(LitIdent { id: "wchar_t".to_owned(), macro_arg: false }),
          }),
          is_struct: false,
        };
        ty.finish(ctx)?;
        ty
      },
    };

    Ok(Some(Type::Ptr { ty: Box::new(ty), mutable: false }))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(
    &self,
    ctx: &mut LocalContext<'_, C>,
    generate_as_array: bool,
  ) -> (TokenStream, TokenStream) {
    enum GenerationMethod {
      /// Generate the string as an array type.
      Array,
      /// Generate the string as a pointer type.
      Ptr,
    }

    let method = if generate_as_array { GenerationMethod::Array } else { GenerationMethod::Ptr };

    match self {
      Self::Ordinary(bytes) => {
        let mut bytes = bytes.clone();
        bytes.push(0);

        let byte_count = proc_macro2::Literal::usize_unsuffixed(bytes.len());
        let byte_string = proc_macro2::Literal::byte_string(&bytes);
        let array_ty = quote! { &[u8; #byte_count] };

        match method {
          GenerationMethod::Array => {
            if ctx.generate_cstr {
              let ffi_prefix = ctx.trait_prefix().map(|trait_prefix| quote! { #trait_prefix::ffi }).into_iter();
              let ty = quote! { #(#ffi_prefix::)*CStr };
              (
                quote! { &#ty },
                quote! {
                  {
                    const BYTES: #array_ty = #byte_string;
                    #[allow(unsafe_code)]
                    unsafe { #ty::from_bytes_with_nul_unchecked(BYTES) }
                  }
                },
              )
            } else {
              (array_ty, quote! { #byte_string })
            }
          },
          GenerationMethod::Ptr => {
            let ffi_prefix = ctx.ffi_prefix().into_iter();
            let ty = quote! { *const #(#ffi_prefix::)*c_char };
            (
              ty.clone(),
              quote! {
                {
                  const BYTES: #array_ty = #byte_string;
                  BYTES.as_ptr() as #ty
                }
              },
            )
          },
        }
      },
      Self::Utf8(s) => {
        let mut bytes = s.as_bytes().to_vec();
        bytes.push(0);

        let byte_count = proc_macro2::Literal::usize_unsuffixed(bytes.len());
        let byte_string = proc_macro2::Literal::byte_string(&bytes);
        let array_ty = quote! { &[u8; #byte_count] };

        match method {
          GenerationMethod::Array => (array_ty, quote! { #byte_string }),
          GenerationMethod::Ptr => (
            quote! { *const u8 },
            quote! {
              {
                const BYTES: #array_ty = #byte_string;
                BYTES.as_ptr()
              }
            },
          ),
        }
      },
      Self::Utf16(s) => {
        let words = s.encode_utf16().chain(std::iter::once(0)).collect::<Vec<_>>();

        let word_count = proc_macro2::Literal::usize_unsuffixed(words.len());
        let word_array = quote! { &[#(#words),*] };
        let array_ty = quote! { &[u16; #word_count] };

        match method {
          GenerationMethod::Array => (array_ty, word_array),
          GenerationMethod::Ptr => (
            quote! { *const u16 },
            quote! {
              {
                const WORDS: #array_ty = #word_array;
                WORDS.as_ptr()
              }
            },
          ),
        }
      },
      Self::Utf32(s) => {
        let dwords = s.chars().map(u32::from).chain(std::iter::once(0)).collect::<Vec<_>>();

        let dword_count = proc_macro2::Literal::usize_unsuffixed(dwords.len());
        let dword_array = quote! { &[#(#dwords),*] };
        let array_ty = quote! { &[u32; #dword_count] };

        match method {
          GenerationMethod::Array => (array_ty, dword_array),
          GenerationMethod::Ptr => (
            quote! { *const u32 },
            quote! {
              {
                const DWORDS: #array_ty = #dword_array;
                DWORDS.as_ptr()
              }
            },
          ),
        }
      },
      Self::Wide(s) => {
        let wchars =
          s.iter().cloned().chain(std::iter::once(0)).map(proc_macro2::Literal::u32_unsuffixed).collect::<Vec<_>>();

        let wchar_ty =
          Type::from_resolved_type(&ctx.resolve_ty("wchar_t").unwrap_or_else(|| "wchar_t".into())).to_token_stream(ctx);
        let wchar_count = proc_macro2::Literal::usize_unsuffixed(wchars.len());
        let wchar_array = quote! { &[#(#wchars as #wchar_ty),*] };
        let array_ty = quote! { &[#wchar_ty; #wchar_count] };

        match method {
          GenerationMethod::Array => (array_ty, wchar_array),
          GenerationMethod::Ptr => (
            quote! { *const #wchar_ty },
            quote! {
              {
                const WCHARS: #array_ty = #wchar_array;
                WCHARS.as_ptr()
              }
            },
          ),
        }
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

  /// Convert the raw string representation to a UTF-8 string, if possible.
  pub(crate) fn as_str(&self) -> Option<&str> {
    match self {
      Self::Ordinary(ref bytes) => str::from_utf8(bytes).ok(),
      Self::Utf8(s) => Some(s.as_str()),
      Self::Utf16(s) => Some(s.as_str()),
      Self::Utf32(s) => Some(s.as_str()),
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

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
}
