use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::char,
  combinator::{map, map_opt, opt, value},
  sequence::{delimited, pair},
  AsChar, Compare, IResult, InputIter, InputTake, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{escaped_char, unescaped_char};
use crate::{ast::tokens::map_token, BuiltInType, CodegenContext, Expr, LitIdent, LocalContext, MacroToken, Type};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LitCharPrefix {
  Utf8,
  Utf16,
  Utf32,
  Wide,
}

impl LitCharPrefix {
  pub fn parse<I, C>(input: I) -> IResult<I, Self>
  where
    I: Debug + InputTake + Slice<RangeFrom<usize>> + InputIter<Item = C> + Compare<&'static str> + Clone,
    C: AsChar,
  {
    alt((
      value(LitCharPrefix::Utf8, tag("u8")),
      value(LitCharPrefix::Utf16, char('u')),
      value(LitCharPrefix::Utf32, char('U')),
      value(LitCharPrefix::Wide, char('L')),
    ))(input)
  }
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
  pub fn parse<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let parse_char = |(prefix, c)| match prefix {
      None if c <= 0xff => Some(LitChar::Ordinary(c as u8)),
      Some(LitCharPrefix::Utf8) if c <= 0x7f => Some(LitChar::Utf8(c as u8)),
      Some(LitCharPrefix::Utf16) if c <= u16::MAX as u32 => Some(LitChar::Utf16(c as u16)),
      Some(LitCharPrefix::Utf32) => Some(LitChar::Utf32(c)),
      Some(LitCharPrefix::Wide) => Some(LitChar::Wide(c)),
      _ => None,
    };

    let delimited_char =
      move |input| delimited(char('\''), alt((escaped_char, map(unescaped_char, u32::from))), char('\''))(input);

    alt((
      map_opt(pair(map_token(LitCharPrefix::parse), map_token(delimited_char)), move |(prefix, c)| {
        parse_char((Some(prefix), c))
      }),
      map_token(map_opt(pair(opt(LitCharPrefix::parse), delimited_char), parse_char)),
    ))(input)
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
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
          name: Box::new(Expr::Variable { name: LitIdent { id: "wchar_t".to_owned() } }),
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

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_set::tokens;

  #[test]
  fn parse_char() {
    let tokens = tokens![r#"'a'"#];
    let (rest, id) = LitChar::parse(tokens).unwrap();
    assert_eq!(id, LitChar::Ordinary(b'a'));
    assert!(rest.is_empty());

    let (_, id) = LitChar::parse(tokens![r#"'\n'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(b'\n'));

    let (_, id) = LitChar::parse(tokens![r#"'\''"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(b'\''));

    let (_, id) = LitChar::parse(tokens![r#"u'\uFFee'"#]).unwrap();
    assert_eq!(id, LitChar::Utf16(0xffee));

    let (_, id) = LitChar::parse(tokens![r#"U'\U0001f369'"#]).unwrap();
    assert_eq!(id, LitChar::Utf32(0x0001f369));

    let (_, id) = LitChar::parse(tokens![r#"U'🍌'"#]).unwrap();
    assert_eq!(id, LitChar::Utf32(0x0001f34c));

    let (_, id) = LitChar::parse(tokens![r#"'\xff'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(0xff));

    let (_, id) = LitChar::parse(tokens![r#"'ÿ'"#]).unwrap();
    assert_eq!(id, LitChar::Ordinary(0xff));
  }
}
