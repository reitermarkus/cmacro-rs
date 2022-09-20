use std::str;

use nom::combinator::{all_consuming, cond, map_opt};
use nom::character::complete::{char, one_of, digit1, hex_digit1, oct_digit1};
use nom::character::{is_hex_digit, is_oct_digit};
use nom::bytes::complete::{is_a, tag, tag_no_case, take_while, take_while_m_n};
use nom::character::complete::none_of;
use nom::multi::fold_many1;
use nom::bytes::complete::is_not;
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

fn escaped_char(input: &[u8]) -> IResult<&[u8], Vec<u8>> {
  alt((
    map(char('a'), |_| vec![b'\x07']),
    map(char('b'), |_| vec![b'\x08']),
    map(char('e'), |_| vec![b'\x1b']),
    map(char('f'), |_| vec![b'\x0c']),
    map(char('n'), |_| vec![b'\n']),
    map(char('r'), |_| vec![b'\r']),
    map(char('t'), |_| vec![b'\t']),
    map(char('v'), |_| vec![b'\x0b']),
    map(one_of([b'\\', b'\'', b'"', b'?']), |c| vec![c as u8]),
    map_opt(take_while_m_n(1, 3, is_oct_digit), |n| {
      str::from_utf8(n).ok()
        .and_then(|s| u8::from_str_radix(s, 8).ok())
        .map(|b| vec![b])
    }),
    preceded(tag_no_case("x"), map_opt(take_while(is_hex_digit), |n: &[u8]| {
      let start = n.len().max(2) - 2;
      str::from_utf8(&n[start..]).ok()
        .and_then(|s| u8::from_str_radix(s, 16).ok())
        .map(|b| vec![b])
    })),
    preceded(char('u'), map_opt(take_while_m_n(4, 4, is_hex_digit), |n: &[u8]| {
      str::from_utf8(n).ok()
        .and_then(|s| u16::from_str_radix(s, 16).ok())
        .map(|n| n.to_be_bytes().to_vec())
    })),
    preceded(char('U'), map_opt(take_while_m_n(8, 8, is_hex_digit), |n: &[u8]| {
      str::from_utf8(n).ok()
        .and_then(|s| u32::from_str_radix(s, 16).ok())
        .map(|n| n.to_be_bytes().to_vec())
    })),
  ))(input)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitChar {
  repr: Vec<u8>,
}

impl LitChar {
  fn from_str(input: &str) -> IResult<&[u8], Vec<u8>> {
    all_consuming(delimited(
      preceded(opt(char('L')), char('\'')),
      fold_many1(
        alt((
          preceded(char('\\'), escaped_char),
          map(none_of(r#"\'"#), |b| vec![b as u8]),
        )),
        Vec::new,
        |mut acc, c| {
          acc.clear();
          acc.extend(c);
          acc
        }
      ),
      char('\''),
    ))(input.as_bytes())
  }

  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(token) = input.first() {
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
    tokens.append_all(match *self.repr.as_slice() {
      [c] => quote! { #c as ::core::ffi::c_char },
      [c1, c2] => {
        let c = u16::from_be_bytes([c1, c2]);
        quote ! { #c as c_wchar }
      },
      [c1, c2, c3, c4] => {
        let c = u32::from_be_bytes([c1, c2, c3, c4]);
        quote! { #c as c_wchar }
      },
      _ => unreachable!(),
    })
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitString {
  pub(crate) repr: Vec<u8>,
}

impl LitString {
  pub fn parse<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(token) = input.first() {
      let input = &input[1..];

      let res: IResult<&[u8], Vec<u8>> = all_consuming(
        delimited(
          preceded(
            opt(alt((terminated(char('u'), char('8')), char('U'), char('L')))),
            char('"'),
          ),
          fold_many0(
            alt((
              preceded(char('\\'), escaped_char),
              map(is_not([b'\\', b'"']), |b: &[u8]| b.to_vec()),
            )),
            Vec::new,
            |mut acc, c| {
              acc.extend(c);
              acc
            },
          ),
          char('"'),
        )
      )(token.as_bytes());

      if let Ok((_, s)) = res {
        return Ok((input, Self { repr: s }))
      }
    }

    Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))
  }
}

impl PartialEq<&str> for LitString {
  fn eq(&self, other: &&str) -> bool {
    self.repr == other.as_bytes()
  }
}

impl ToTokens for LitString {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    let mut bytes = self.repr.clone();
    bytes.push(0);
    let bytes = syn::LitByteStr::new(&bytes, Span::call_site());

    tokens.append_all(quote! {
      {
        const CSTR: &::core::ffi::CStr = ::core::ffi::CStr::from_bytes_with_nul_unchecked(&#bytes);
        CSTR.as_ptr()
      }
    })
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

    let (input, (repr, size)) = all_consuming(float)(input)?;
    Ok((input, (repr, size)))
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(Ok((_, (repr, size1)))) = tokens.first().copied().map(Self::from_str) {
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
      let _size = size1.or(size2);

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

    dbg!(input);

    let suffix = alt((
      map(
        pair(
          tag_no_case("u"),
          opt(
            alt((
              tag_no_case("ll"),
              tag_no_case("l"),
              tag_no_case("z"),
            )),
          ),
        ),
        |(unsigned, size)| (Some(unsigned), size)
      ),
      map(
        pair(
          alt((
            tag_no_case("ll"),
            tag_no_case("l"),
            tag_no_case("z"),
          )),
          opt(tag_no_case("u")),
        ),
        |(size, unsigned)| (unsigned, Some(size)),
      ),
      map(eof, |_| (None, None))
    ));

    let (input, (repr, (unsigned, size))) = all_consuming(pair(digits, suffix))(input)?;
    Ok((input, (repr, unsigned, size)))
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    if let Some(Ok((_, (repr, unsigned1, size1)))) = tokens.first().copied().map(Self::from_str) {
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
      let _unsigned = unsigned1.or(unsigned2).is_some();
      let _size = size1.or(size2);

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
    let (_, id) = LitFloat::parse(&[r#"1234f"#]).unwrap();
    assert_eq!(id, LitFloat { repr: "1234".into() });

    let (_, id) = LitFloat::parse(&[r#"12.34f"#]).unwrap();
    assert_eq!(id, LitFloat { repr: "12.34".into() });

    let (_, id) = LitFloat::parse(&[r#"12.34L"#]).unwrap();
    assert_eq!(id, LitFloat { repr: "12.34".into() });
  }

  #[test]
  fn parse_int() {
    let (_, id) = LitInt::parse(&[r#"777"#]).unwrap();
    assert_eq!(id, LitInt { repr: "777".into() });

    let (_, id) = LitInt::parse(&[r#"0777"#]).unwrap();
    assert_eq!(id, LitInt { repr: "0o777".into() });

    let (_, id) = LitInt::parse(&[r#"8718937817238719"#]).unwrap();
    assert_eq!(id, LitInt { repr: "8718937817238719".into() });

    let (_, id) = LitInt::parse(&[r#"1U"#]).unwrap();
    assert_eq!(id, LitInt { repr: "1".into() });

    let (_, id) = LitInt::parse(&[r#"1ULL"#]).unwrap();
    assert_eq!(id, LitInt { repr: "1".into() });

    let (_, id) = LitInt::parse(&[r#"1UL"#]).unwrap();
    assert_eq!(id, LitInt { repr: "1".into() });

    let (_, id) = LitInt::parse(&[r#"1LLU"#]).unwrap();
    assert_eq!(id, LitInt { repr: "1".into() });

    let (_, id) = LitInt::parse(&[r#"1z"#]).unwrap();
    assert_eq!(id, LitInt { repr: "1".into() });
  }
}
