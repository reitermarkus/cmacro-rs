use std::{
  fmt::Debug,
  ops::{Add, Div, Mul, RangeFrom, RangeTo, Sub},
  str,
};

use nom::{
  branch::alt,
  bytes::complete::tag_no_case,
  character::complete::{char, digit1},
  combinator::{all_consuming, cond, map, opt, recognize},
  sequence::{delimited, pair, preceded, tuple},
  AsChar, Compare, CompareResult, FindSubstring, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition,
  Offset, ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
use std::num::FpCategory;

use super::{meta, take_one, token};
use crate::{BuiltInType, CodegenContext, LocalContext, Type};

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
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
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
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
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
    let trait_prefix = ctx.trait_prefix().into_iter();
    tokens.append_all(match self {
      Self::Float(f) => match f.classify() {
        FpCategory::Nan => quote! { #(#trait_prefix::)*f32::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #(#trait_prefix::)*f32::INFINITY }
          } else {
            quote! { #(#trait_prefix::)*f32::NEG_INFINITY }
          }
        },
        FpCategory::Zero | FpCategory::Subnormal | FpCategory::Normal => {
          proc_macro2::Literal::f32_unsuffixed(f).to_token_stream()
        },
      },
      Self::Double(f) | Self::LongDouble(f) => match f.classify() {
        FpCategory::Nan => quote! { #(#trait_prefix::)*f64::NAN },
        FpCategory::Infinite => {
          if f.is_sign_positive() {
            quote! { #(#trait_prefix::)*f64::INFINITY }
          } else {
            quote! { #(#trait_prefix::)*f64::NEG_INFINITY }
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

#[cfg(test)]
mod tests {
  use super::*;

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
}
