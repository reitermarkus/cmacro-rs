use std::str;

use nom::combinator::{all_consuming, cond, map_res, map_opt};
use nom::character::complete::{char, anychar, one_of, digit1, hex_digit1, oct_digit1};
use nom::character::{is_hex_digit, is_oct_digit};
use nom::bytes::complete::{is_a, tag, tag_no_case, take_while, take_while_m_n};
use quote::{ToTokens, TokenStreamExt};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
  Char(LitChar),
  String(LitString),
  Float(LitFloat),
  Int(LitInt),
}

impl Lit {
  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    alt((
      map(LitChar::parse, Self::Char),
      map(LitString::parse, Self::String),
      map(LitFloat::parse, Self::Float),
      map(LitInt::parse, Self::Int),
    ))(input)
  }
}

impl ToTokens for Lit {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    match self {
      Self::Char(c) => c.to_tokens(tokens),
      Self::String(s) => s.to_tokens(tokens),
      Self::Float(f) => f.to_tokens(tokens),
      Self::Int(i) => i.to_tokens(tokens),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitChar {
  repr: char,
}

impl LitChar {
  fn unescaped_char(input: &[u8]) -> IResult<&[u8], char> {
    map_opt(anychar, |c| if c == '\\' { None } else { Some(c) })(input)
  }

  fn escaped_char(input: &[u8]) -> IResult<&[u8], char> {
    preceded(
      char('\\'),
      alt((
        map(char('a'), |_| '\x07'),
        map(char('b'), |_| '\x08'),
        map(char('e'), |_| '\x1b'),
        map(char('f'), |_| '\x0c'),
        map(char('n'), |_| '\n'),
        map(char('r'), |_| '\r'),
        map(char('t'), |_| '\t'),
        map(char('v'), |_| '\x0b'),
        one_of(r#"\'"?"#),
        map_res(take_while_m_n(1, 3, is_oct_digit), |n| {
          let s = str::from_utf8(n).unwrap();
          u8::from_str_radix(s, 8).map(|b| b as char)
        }),
        preceded(tag_no_case("x"), map_res(take_while(is_hex_digit), |n: &[u8]| {
          let start = n.len().max(2) - 2;
          let s = str::from_utf8(&n[start..]).unwrap();
          u8::from_str_radix(s, 16).map(|b| b as char)
        })),
        preceded(tag_no_case("u"), map_opt(take_while_m_n(4, 4, is_hex_digit), |n: &[u8]| {
          let s = str::from_utf8(n).unwrap();
          u32::from_str_radix(s, 16).ok().and_then(|b| char::from_u32(b))
        })),
        preceded(tag_no_case("U"), map_opt(take_while_m_n(8, 8, is_hex_digit), |n: &[u8]| {
          let s = str::from_utf8(n).unwrap();
          u32::from_str_radix(s, 16).ok().and_then(|b| char::from_u32(b))
        })),
      )
    ))(input)
  }

  fn from_str(input: &str) -> IResult<&[u8], char> {
    all_consuming(delimited(
      char('\''),
      alt((
        Self::escaped_char,
        Self::unescaped_char,
      )),
      char('\''),
    ))(input.as_bytes())
  }

  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(token) = input.get(0) {
      let input = &input[1..];

      if let Ok((_, c)) = Self::from_str(token) {
        return Ok((input, Self { repr: c }))
      }
    }

    Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))
  }
}

impl ToTokens for LitChar {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    self.repr.to_tokens(tokens)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitString {
  pub(crate) repr: String,
}

impl LitString {
  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(token) = input.get(0) {
      let input = &input[1..];

      if token.starts_with("\"") && token.ends_with("\"") {
        return Ok((input, Self { repr: token[1..(token.len() - 1)].to_owned() }))
      }
    }

    Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))
  }
}

impl PartialEq<&str> for LitString {
  fn eq(&self, other: &&str) -> bool {
    self.repr == *other
  }
}

impl ToTokens for LitString {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    self.repr.to_tokens(tokens)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitFloat {
  repr: String
}

impl LitFloat {
  fn from_str(input: &str) -> IResult<&str, (String, Option<&str>)> {
    let float = alt((
      map(
        pair(digit1, tag_no_case("f")),
        |(int, suffix): (&str, &str)| (int.to_owned(), Some(suffix)),
      ),
      map(
        tuple((digit1, preceded(char('.'), digit1), opt(alt((tag_no_case("f"), tag_no_case("l")))))),
        |(int, dec, suffix): (&str, &str, Option<&str>)| (format!("{}.{}", int, dec), suffix),
      ),
    ));

    let (input, (repr, size)) = terminated(float, eof)(input)?;
    Ok((input, (repr, size)))
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(Ok((_, (repr, size1)))) = tokens.get(0).copied().map(Self::from_str) {
      let tokens = &tokens[1..];

      let suffix_f = alt((token("f"), token("F")));
      let suffix_long = alt((token("l"), token("L")));

      let mut suffix = map(
        alt((
          cond(size1.is_none(), opt(preceded(delimited(meta, token("##"), meta), suffix_f))),
          cond(size1.is_none() && repr.contains("."), opt(preceded(delimited(meta, token("##"), meta), suffix_long)))
        )),
        |size| size.flatten()
      );

      let (tokens, size2) = suffix(tokens)?;
      let _size = size1.or_else(|| size2);

      // TODO: Handle suffix.
      return Ok((tokens, Self { repr }))
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
  }

}


impl ToTokens for LitFloat {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(self.repr.parse::<TokenStream>().unwrap())
  }
}

/// An integer literal.
///
/// ```c
/// #define MY_INT1 1ull
/// #define MY_INT2 1u ## LL
/// #define MY_INT3 1 ## ULL
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitInt {
  repr: String,
}

impl LitInt {
  pub fn new(s: &str) -> Self {
    let (_, (repr, _, _)) = Self::from_str(s).unwrap();
    Self { repr }
  }

  fn from_str(input: &str) -> IResult<&str, (String, Option<&str>, Option<&str>)> {
    let digits = alt((
      map(preceded(tag_no_case("0x"), hex_digit1), |n| format!("0x{}", n)),
      map(preceded(tag_no_case("0b"), is_a("01")), |n| format!("0b{}", n)),
      map(preceded(tag("0"), oct_digit1), |n| format!("0o{}", n)),
      map(digit1, |n: &str| n.to_owned()),
    ));

    let suffix_unsigned = tag_no_case("u");
    let suffix_long = tag_no_case("l");
    let suffix_long_long = tag_no_case("ll");
    let suffix_size_t = tag_no_case("z");

    let suffix = permutation((
      opt(map(suffix_unsigned, |_| "u")),
      opt(
        alt((
          suffix_long_long,
          suffix_long,
          suffix_size_t,
        ))
      )
    ));

    let (input, (repr, (unsigned, size))) = terminated(pair(digits, suffix), eof)(input)?;
    Ok((input, (repr, unsigned, size)))
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(Ok((_, (repr, unsigned1, size1)))) = tokens.get(0).copied().map(Self::from_str) {
      let tokens = &tokens[1..];

      let suffix_unsigned = alt((token("u"), token("U")));
      let suffix_long = alt((token("l"), token("L")));
      let suffix_long_long = alt((token("ll"), token("LL")));
      let suffix_size_t = alt((token("z"), token("Z")));

      let mut suffix = map(
        permutation((
          cond(unsigned1.is_none(), opt(preceded(delimited(meta, token("##"), meta), suffix_unsigned))),
          cond(size1.is_none(), opt(preceded(delimited(meta, token("##"), meta), alt((
            suffix_long_long,
            suffix_long,
            suffix_size_t,
          )))))
        )),
        |(unsigned, size)| (unsigned.flatten(), size.flatten()),
      );

      let (tokens, (unsigned2, size2)) = suffix(tokens)?;
      let _unsigned = unsigned1.is_some() || unsigned2.is_some();
      let _size = size1.or_else(|| size2);

      // TODO: Handle suffix.
      return Ok((tokens, Self { repr }))
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
  }
}

impl ToTokens for LitInt {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(self.repr.parse::<TokenStream>().unwrap())
  }
}
