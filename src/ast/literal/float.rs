use std::{
  fmt::Debug,
  ops::{Add, Div, Mul, RangeFrom, RangeTo, Sub},
  str,
};

use nom::{
  branch::alt,
  bytes::complete::tag_no_case,
  character::complete::{char, digit1},
  combinator::{all_consuming, map_opt, opt, recognize, value},
  sequence::{pair, tuple},
  AsChar, Compare, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset, ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
use std::num::FpCategory;

use crate::{ast::tokens::take_one, BuiltInType, CodegenContext, Lit, LocalContext, MacroToken, Type};

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum LitFloatSuffix {
  Float,
  LongDouble,
}

impl LitFloatSuffix {
  pub fn parse<I, C>(input: I) -> IResult<I, Self>
  where
    I: InputTake + InputIter<Item = C> + Compare<&'static str> + Clone,
    C: AsChar,
  {
    alt((value(Self::Float, tag_no_case("f")), value(Self::LongDouble, tag_no_case("l"))))(input)
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
  pub(crate) fn parse_str<I, C>(input: I) -> IResult<I, Self>
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
      + ParseTo<f32>
      + ParseTo<f64>
      + Clone,
    C: AsChar,
  {
    let decimal = |input: I| recognize(pair(char('.'), digit1))(input);
    let scientific = |input: I| recognize(tuple((tag_no_case("e"), opt(alt((char('+'), char('-')))), digit1)))(input);

    map_opt(
      pair(
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
        opt(LitFloatSuffix::parse),
      ),
      |(repr, size)| match size {
        Some(LitFloatSuffix::Float) => repr.parse_to().map(Self::Float),
        Some(LitFloatSuffix::LongDouble) => repr.parse_to().map(Self::LongDouble),
        _ => repr.parse_to().map(Self::Double),
      },
    )(input)
  }

  /// Parse a floating-point literal.
  pub fn parse<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    map_opt(take_one, |token| if let MacroToken::Lit(Lit::Float(lit)) = token { Some(*lit) } else { None })(tokens)
  }

  #[allow(unused_variables)]
  pub(crate) fn finish<'t, C>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    Ok(Some(match self {
      Self::Float(_) => Type::BuiltIn(BuiltInType::Float),
      Self::Double(_) => Type::BuiltIn(BuiltInType::Double),
      Self::LongDouble(_) => Type::BuiltIn(BuiltInType::LongDouble),
    }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
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

impl<'t> TryFrom<&'t str> for LitFloat {
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
  fn parse_float() {
    assert_eq!(LitFloat::try_from("12.34"), Ok(LitFloat::Double(12.34)));

    assert_eq!(LitFloat::try_from("12.34f"), Ok(LitFloat::Float(12.34)));

    assert_eq!(LitFloat::try_from("12.34L"), Ok(LitFloat::LongDouble(12.34)));

    assert_eq!(LitFloat::try_from(".1"), Ok(LitFloat::Double(0.1)));

    assert_eq!(LitFloat::try_from("1."), Ok(LitFloat::Double(1.0)));

    assert_eq!(LitFloat::try_from("1e1"), Ok(LitFloat::Double(10.0)));

    assert_eq!(LitFloat::try_from("1e-1f"), Ok(LitFloat::Float(0.1)));
  }
}
