use std::{
  borrow::Cow,
  fmt::Debug,
  iter,
  str::{self, Utf8Error},
  string::FromUtf16Error,
};

use nom::{
  branch::alt,
  bytes::complete::{is_not, tag},
  character::complete::{char, none_of},
  combinator::{all_consuming, map, map_opt, map_res, opt},
  multi::{fold_many0, many0},
  sequence::{delimited, preceded},
  IResult,
};
use proc_macro2::TokenStream;
use quote::quote;

use crate::{BuiltInType, CodegenContext, Expr, Lit, LocalContext, MacroToken, Type, TypeQualifier, Var};

use crate::ast::{
  tokens::{id, take_one},
  Identifier,
};

use super::escaped_char;

/// A string literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LitString<'t> {
  /// An ordinary string (`const char*`) literal.
  ///
  /// ```c
  /// #define STRING "abc"
  /// ```
  Ordinary(Cow<'t, [u8]>),
  /// A UTF-8 string (`const char8_t*`) literal.
  ///
  /// ```c
  /// #define STRING u8"def"
  /// ```
  Utf8(Cow<'t, str>),
  /// A UTF-16 string (`const char16_t*`) literal.
  ///
  /// ```c
  /// #define STRING u"ghi"
  /// ```
  Utf16(Cow<'t, str>),
  /// A UTF-32 string (`const char32_t*`) literal.
  ///
  /// ```c
  /// #define STRING U"jkl"
  /// ```
  Utf32(Cow<'t, str>),
  /// A wide string (`const wchar_t*`) literal.
  ///
  /// ```c
  /// #define STRING L"mno"
  /// ```
  Wide(Vec<u32>),
}

impl<'t> LitString<'t> {
  /// Parse
  fn parse_ordinary(input: &str) -> IResult<&str, Cow<'_, [u8]>> {
    delimited(
      char('\"'),
      fold_many0(
        alt((
          map_opt(escaped_char, |c| {
            if let Ok(c) = u8::try_from(c) {
              Some(Cow::Owned(vec![c]))
            } else if let Ok(c) = char::try_from(c) {
              let mut s = [0; 4];
              Some(Cow::Owned(c.encode_utf8(&mut s).as_bytes().to_vec()))
            } else {
              None
            }
          }),
          map(is_not("\\\"\n"), |b: &str| Cow::Borrowed(b.as_bytes())),
        )),
        || Cow::Borrowed(&[] as &[u8]),
        |mut acc: Cow<'_, [u8]>, c| {
          if acc.as_ref().is_empty() {
            c
          } else {
            acc.to_mut().extend(c.as_ref());
            acc
          }
        },
      ),
      char('\"'),
    )(input)
  }

  fn parse_utf8(input: &str) -> IResult<&str, Cow<'_, str>> {
    map_res(Self::parse_ordinary, |bytes| -> Result<Cow<'_, str>, Utf8Error> {
      match bytes {
        Cow::Borrowed(bytes) => Ok(Cow::Borrowed(str::from_utf8(bytes)?)),
        Cow::Owned(bytes) => Ok(Cow::Owned(String::from_utf8(bytes).map_err(|e| e.utf8_error())?)),
      }
    })(input)
  }

  fn parse_utf16(input: &str) -> IResult<&str, Cow<'_, str>> {
    enum Part<'s> {
      Vec(Vec<u16>),
      String(Cow<'s, str>),
    }

    impl<'s> Part<'s> {
      fn into_vec(self) -> Vec<u16> {
        match self {
          Self::Vec(vec) => vec,
          Self::String(s) => s.as_ref().encode_utf16().collect(),
        }
      }
    }

    map_res(
      delimited(
        char('\"'),
        fold_many0(
          alt((
            map_opt(escaped_char, |c| {
              if let Ok(c) = u16::try_from(c) {
                Some(Part::Vec(vec![c]))
              } else if let Ok(c) = char::try_from(c) {
                let mut s = [0; 2];
                Some(Part::Vec(c.encode_utf16(&mut s).to_vec()))
              } else {
                None
              }
            }),
            map(is_not("\\\"\n"), |s: &str| Part::String(Cow::Borrowed(s))),
          )),
          || Part::String(Cow::Borrowed("")),
          |acc, c| match (acc, c) {
            (Part::String(s), c) if s.as_ref().is_empty() => c,
            (Part::String(mut s), Part::String(c)) => {
              s.to_mut().push_str(c.as_ref());
              Part::String(s)
            },
            (s, c) => {
              let mut acc = s.into_vec();
              acc.extend(c.into_vec());
              Part::Vec(acc)
            },
          },
        ),
        char('\"'),
      ),
      |part| -> Result<Cow<'_, str>, FromUtf16Error> {
        match part {
          Part::String(s) => Ok(s),
          Part::Vec(v) => Ok(Cow::Owned(String::from_utf16(&v)?)),
        }
      },
    )(input)
  }

  fn parse_utf32(input: &str) -> IResult<&str, Cow<'_, str>> {
    enum Part<'s> {
      Char(char),
      String(Cow<'s, str>),
    }

    delimited(
      char('\"'),
      fold_many0(
        alt((
          map_res(escaped_char, |c| char::try_from(c).map(Part::Char)),
          map(is_not("\\\"\n"), |s| Part::String(Cow::Borrowed(s))),
        )),
        || Cow::Borrowed(""),
        |mut acc, c| match c {
          Part::Char(c) => {
            acc.to_mut().push(c);
            acc
          },
          Part::String(s) => {
            if acc.as_ref().is_empty() {
              s
            } else {
              acc.to_mut().push_str(s.as_ref());
              acc
            }
          },
        },
      ),
      char('\"'),
    )(input)
  }

  fn parse_wide(input: &str) -> IResult<&str, Vec<u32>> {
    delimited(char('\"'), many0(alt((escaped_char, map(none_of("\\\"\n"), u32::from)))), char('\"'))(input)
  }

  pub(crate) fn parse_str(input: &'t str) -> IResult<&'t str, Self> {
    alt((
      map(Self::parse_ordinary, Self::Ordinary),
      preceded(tag("u8"), map(Self::parse_utf8, Self::Utf8)),
      preceded(tag("u"), map(Self::parse_utf16, Self::Utf16)),
      preceded(tag("U"), map(Self::parse_utf32, Self::Utf32)),
      preceded(tag("L"), map(Self::parse_wide, Self::Wide)),
    ))(input)
  }

  /// Parse a string literal.
  pub fn parse<'i>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (input, s) =
      map_opt(take_one, |token| if let MacroToken::Lit(Lit::String(s)) = token { Some(s.clone()) } else { None })(
        input,
      )?;

    match s {
      Self::Ordinary(bytes) => map(
        fold_many0(
          map_opt(take_one, |token| match token {
            MacroToken::Lit(Lit::String(LitString::Ordinary(bytes))) => Some(Cow::Borrowed(bytes.as_ref())),
            _ => None,
          }),
          move || bytes.clone(),
          |mut acc, bytes| {
            acc.to_mut().extend(bytes.as_ref());
            acc
          },
        ),
        Self::Ordinary,
      )(input),
      Self::Utf8(s) => map(
        fold_many0(
          alt((
            map_opt(take_one, |token| match token {
              MacroToken::Lit(Lit::String(LitString::Utf8(s))) => Some(Cow::Borrowed(s.as_ref())),
              _ => None,
            }),
            preceded(
              opt(id("u8")),
              map_opt(take_one, |token| match token {
                MacroToken::Lit(Lit::String(LitString::Ordinary(bytes))) => {
                  Some(Cow::Borrowed(str::from_utf8(bytes.as_ref()).ok()?))
                },
                _ => None,
              }),
            ),
          )),
          move || s.clone(),
          |mut acc, s| {
            acc.to_mut().push_str(s.as_ref());
            acc
          },
        ),
        Self::Utf8,
      )(input),
      Self::Utf16(s) => map(
        fold_many0(
          alt((
            map_opt(take_one, |token| match token {
              MacroToken::Lit(Lit::String(LitString::Utf16(s))) => Some(Cow::Borrowed(s.as_ref())),
              _ => None,
            }),
            preceded(
              opt(id("u")),
              map_opt(take_one, |token| match token {
                MacroToken::Lit(Lit::String(LitString::Ordinary(bytes))) => {
                  Some(Cow::Borrowed(str::from_utf8(bytes.as_ref()).ok()?))
                },
                _ => None,
              }),
            ),
          )),
          move || s.clone(),
          |mut acc, s| {
            acc.to_mut().push_str(s.as_ref());
            acc
          },
        ),
        Self::Utf16,
      )(input),
      Self::Utf32(s) => map(
        fold_many0(
          alt((
            map_opt(take_one, |token| match token {
              MacroToken::Lit(Lit::String(LitString::Utf32(s))) => Some(Cow::Borrowed(s.as_ref())),
              _ => None,
            }),
            preceded(
              opt(id("U")),
              map_opt(take_one, |token| match token {
                MacroToken::Lit(Lit::String(LitString::Ordinary(bytes))) => {
                  Some(Cow::Borrowed(str::from_utf8(bytes.as_ref()).ok()?))
                },
                _ => None,
              }),
            ),
          )),
          move || s.clone(),
          |mut acc, s| {
            acc.to_mut().push_str(&s);
            acc
          },
        ),
        Self::Utf32,
      )(input),
      Self::Wide(words) => map(
        fold_many0(
          alt((
            map_opt(take_one, |token| match token {
              MacroToken::Lit(Lit::String(LitString::Wide(words))) => Some(Cow::Borrowed(words)),
              _ => None,
            }),
            preceded(
              opt(id("L")),
              map_opt(take_one, |token| match token {
                MacroToken::Lit(Lit::String(LitString::Ordinary(bytes))) => {
                  Some(Cow::Owned(bytes.as_ref().iter().map(|b| u32::from(*b)).collect::<Vec<_>>()))
                },
                _ => None,
              }),
            ),
          )),
          move || words.clone(),
          |mut acc, words| {
            acc.extend(words.as_ref());
            acc
          },
        ),
        Self::Wide,
      )(input),
    }
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
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
          name: Box::new(Expr::Var(Var { name: Identifier { id: "wchar_t".to_owned().into() } })),
          is_struct: false,
        };
        ty.finish(ctx)?;
        ty
      },
    };

    Ok(Some(Type::Qualified { ty: Box::new(Type::Ptr { ty: Box::new(ty) }), qualifier: TypeQualifier::Const }))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(
    &self,
    ctx: &mut LocalContext<'_, '_, C>,
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
        let mut bytes = bytes.clone().into_owned();
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
        let words = s.encode_utf16().chain(iter::once(0)).collect::<Vec<_>>();

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
        let dwords = s.as_ref().chars().map(u32::from).chain(iter::once(0)).collect::<Vec<_>>();

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
          s.iter().cloned().chain(iter::once(0)).map(proc_macro2::Literal::u32_unsuffixed).collect::<Vec<_>>();

        let wchar_ty = if let Some(ty) = ctx.resolve_ty("wchar_t") {
          Type::from_rust_ty(&ty, ctx.ffi_prefix().as_ref()).unwrap().to_token_stream(ctx)
        } else {
          quote! { wchar_t }
        };

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
      Self::Ordinary(bytes) => Some(bytes.as_ref()),
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
      Self::Utf8(s) => Some(s.as_ref()),
      Self::Utf16(s) => Some(s.as_ref()),
      Self::Utf32(s) => Some(s.as_ref()),
      _ => None,
    }
  }

  pub(crate) fn into_static(self) -> LitString<'static> {
    match self {
      Self::Ordinary(bytes) => LitString::Ordinary(Cow::Owned(bytes.into_owned())),
      Self::Utf8(s) => LitString::Utf8(Cow::Owned(s.into_owned())),
      Self::Utf16(s) => LitString::Utf16(Cow::Owned(s.into_owned())),
      Self::Utf32(s) => LitString::Utf32(Cow::Owned(s.into_owned())),
      Self::Wide(words) => LitString::Wide(words),
    }
  }
}

impl<'t> TryFrom<&'t str> for LitString<'t> {
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
  fn parse_string() {
    assert_eq!(LitString::try_from(r#""asdf""#), Ok(LitString::Ordinary("asdf".as_bytes().into())));

    assert_eq!(LitString::try_from(r#""\360\237\216\247🎧""#), Ok(LitString::Ordinary("🎧🎧".as_bytes().into())));

    assert_eq!(LitString::try_from(r#""abc\ndef""#), Ok(LitString::Ordinary("abc\ndef".as_bytes().into())));

    assert_eq!(
      LitString::try_from(r#""escaped\"quote""#),
      Ok(LitString::Ordinary(r#"escaped"quote"#.as_bytes().into()))
    );

    assert_eq!(LitString::try_from(r#"u8"🎧\xf0\x9f\x8e\xa4""#), Ok(LitString::Utf8("🎧🎤".into())));

    assert_eq!(LitString::try_from(r#"u8"Put your 🎧 on.""#), Ok(LitString::Utf8("Put your 🎧 on.".into())));

    assert_eq!(LitString::try_from(r#"u"🎧\uD83C\uDFA4""#), Ok(LitString::Utf16("🎧🎤".into())));

    assert_eq!(LitString::try_from(r#"U"🎧\U0001F3A4""#), Ok(LitString::Utf32("🎧🎤".into())));
  }

  #[test]
  fn parse_unprefixed_utf32() {
    assert_eq!(
      LitString::try_from(r#""\U00020402""#),
      Ok(LitString::Ordinary(Cow::Borrowed(&[0o360, 0o240, 0o220, 0o202])))
    )
  }
}
