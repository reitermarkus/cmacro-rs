use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  branch::{alt, permutation},
  combinator::{map, opt},
  multi::fold_many0,
  sequence::{delimited, pair, preceded, terminated},
  AsChar, Compare, FindSubstring, IResult, InputIter, InputLength, InputTake, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};

use super::*;
use crate::{CodegenContext, LocalContext};

/// A built-in type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltInType {
  /// `float`
  Float,
  /// `double`
  Double,
  /// `long double`
  LongDouble,
  /// `bool`
  Bool,
  /// `char`
  Char,
  /// `signed char`
  SChar,
  /// `unsigned char`
  UChar,
  /// `short`
  Short,
  /// `unsigned short`
  UShort,
  /// `int`
  Int,
  /// `unsigned int`
  UInt,
  /// `long`
  Long,
  /// `unsigned long`
  ULong,
  /// `long long`
  LongLong,
  /// `unsigned long long`
  ULongLong,
  /// `void`
  Void,
}

impl ToTokens for BuiltInType {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Float => quote! { f32 },
      Self::Double => quote! { f64 },
      Self::LongDouble => quote! { c_longdouble },
      Self::Bool => quote! { bool },
      Self::Char => quote! { c_char },
      Self::SChar => quote! { c_schar },
      Self::UChar => quote! { c_uchar },
      Self::Short => quote! { c_short },
      Self::UShort => quote! { c_ushort },
      Self::Int => quote! { c_int },
      Self::UInt => quote! { c_uint },
      Self::Long => quote! { c_long },
      Self::ULong => quote! { c_ulong },
      Self::LongLong => quote! { c_longlong },
      Self::ULongLong => quote! { c_ulonglong },
      Self::Void => quote! { c_void },
    })
  }
}

fn int_ty<I>(input: &[I]) -> IResult<&[I], BuiltInType>
where
  I: Debug + InputTake + InputLength + Slice<std::ops::RangeFrom<usize>> + Compare<&'static str> + Clone,
{
  fn int_signedness<I>(input: &[I]) -> IResult<&[I], &'static str>
  where
    I: Debug + InputTake + InputLength + Slice<std::ops::RangeFrom<usize>> + Compare<&'static str> + Clone,
  {
    alt((keyword("unsigned"), keyword("signed")))(input)
  }

  fn int_longness<I>(input: &[I]) -> IResult<&[I], &'static str>
  where
    I: Debug + InputTake + InputLength + Slice<std::ops::RangeFrom<usize>> + Compare<&'static str> + Clone,
  {
    alt((keyword("short"), keyword("long")))(input)
  }

  alt((
    // [const] [(unsigned | signed)] long long [int]
    map(
      permutation((const_qualifier, opt(int_signedness), keyword("long"), keyword("long"), opt(keyword("int")))),
      |(_, s, _, _, _)| {
        if matches!(s, Some("unsigned")) {
          BuiltInType::ULongLong
        } else {
          BuiltInType::LongLong
        }
      },
    ),
    // [const] [(unsigned | signed)] (long | short) [int]
    map(permutation((const_qualifier, opt(int_signedness), int_longness, opt(keyword("int")))), |(_, s, i, _)| match (
      s, i,
    ) {
      (Some("unsigned"), "short") => BuiltInType::UShort,
      (_, "short") => BuiltInType::Short,
      (Some("unsigned"), "long") => BuiltInType::ULong,
      (_, "long") => BuiltInType::Long,
      _ => unreachable!(),
    }),
    // [const] [(unsigned | signed)] (char | int)
    map(
      permutation((const_qualifier, opt(int_signedness), alt((keyword("char"), keyword("int"))))),
      |(_, s, i)| match (s, i) {
        (Some("unsigned"), "int") => BuiltInType::UInt,
        (_, "int") => BuiltInType::Int,
        (Some("unsigned"), "char") => BuiltInType::UChar,
        (Some("signed"), "char") => BuiltInType::SChar,
        (_, "char") => BuiltInType::Char,
        _ => unreachable!(),
      },
    ),
  ))(input)
}

fn ty<I>(input: &[I]) -> IResult<&[I], Type>
where
  I: Debug + InputTake + InputLength + InputIter + Slice<RangeFrom<usize>> + Compare<&'static str> + Clone,
  <I as InputIter>::Item: AsChar,
{
  alt((
    // [const] (float | [long] double | bool | void)
    map(
      delimited(
        const_qualifier,
        alt((
          map(keyword("void"), |_| BuiltInType::Void),
          map(keyword("bool"), |_| BuiltInType::Bool),
          map(keyword("float"), |_| BuiltInType::Float),
          map(pair(terminated(opt(keyword("long")), const_qualifier), keyword("double")), |(long, _)| {
            if long.is_some() {
              BuiltInType::LongDouble
            } else {
              BuiltInType::Double
            }
          }),
        )),
        const_qualifier,
      ),
      Type::BuiltIn,
    ),
    map(int_ty, Type::BuiltIn),
    // [const] <identifier>
    map(delimited(const_qualifier, pair(opt(keyword("struct")), identifier), const_qualifier), |(s, id)| {
      Type::Identifier { name: Identifier::Literal(id), is_struct: s.is_some() }
    }),
  ))(input)
}

fn const_qualifier<I>(input: &[I]) -> IResult<&[I], bool>
where
  I: Debug + InputTake + InputLength + Slice<std::ops::RangeFrom<usize>> + Compare<&'static str> + Clone,
{
  fold_many0(keyword("const"), || false, |_, _| true)(input)
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  /// A built-in type.
  BuiltIn(BuiltInType),
  /// A type identifier.
  #[allow(missing_docs)]
  Identifier { name: Identifier, is_struct: bool },
  /// A pointer type.
  #[allow(missing_docs)]
  Ptr { ty: Box<Self>, mutable: bool },
}

impl Type {
  /// Parse a type.
  pub fn parse<I>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter
      + Slice<RangeFrom<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + Clone,
    <I as InputIter>::Item: AsChar,
  {
    let (tokens, ty) = delimited(const_qualifier, ty, const_qualifier)(tokens)?;

    fold_many0(
      preceded(pair(token("*"), meta), const_qualifier),
      move || ty.clone(),
      |acc, is_const| Type::Ptr { ty: Box::new(acc), mutable: !is_const },
    )(tokens)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    match self {
      Self::BuiltIn(_) => Ok(None),
      Self::Identifier { name, .. } => {
        name.finish(ctx)?;

        if let Identifier::Literal(id) = name {
          if let Some(ty) = ctx.resolve_ty(id.as_str()) {
            match ty.as_str() {
              "float" => {
                *self = Type::BuiltIn(BuiltInType::Float);
              },
              "double" => {
                *self = Type::BuiltIn(BuiltInType::Double);
              },
              "long double" => {
                *self = Type::BuiltIn(BuiltInType::LongDouble);
              },
              "bool" => {
                *self = Type::BuiltIn(BuiltInType::Bool);
              },
              "char" => {
                *self = Type::BuiltIn(BuiltInType::Char);
              },
              "signed char" => {
                *self = Type::BuiltIn(BuiltInType::SChar);
              },
              "unsigned char" => {
                *self = Type::BuiltIn(BuiltInType::UChar);
              },
              "short" => {
                *self = Type::BuiltIn(BuiltInType::Short);
              },
              "unsigned short" => {
                *self = Type::BuiltIn(BuiltInType::UShort);
              },
              "int" => {
                *self = Type::BuiltIn(BuiltInType::Int);
              },
              "unsigned int" => {
                *self = Type::BuiltIn(BuiltInType::UInt);
              },
              "long" => {
                *self = Type::BuiltIn(BuiltInType::Long);
              },
              "unsigned long" => {
                *self = Type::BuiltIn(BuiltInType::ULong);
              },
              "long long" => {
                *self = Type::BuiltIn(BuiltInType::LongLong);
              },
              "unsigned long long" => {
                *self = Type::BuiltIn(BuiltInType::ULongLong);
              },
              "void" => {
                *self = Type::BuiltIn(BuiltInType::Void);
              },
              _ => {
                *self = Type::Identifier { name: Identifier::Literal(ty), is_struct: false };
              },
            }

            return self.finish(ctx)
          }
        }

        Ok(None)
      },
      Self::Ptr { ty, .. } => ty.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::BuiltIn(ty) => match ty {
        BuiltInType::Float | BuiltInType::Double | BuiltInType::Bool => ty.to_tokens(tokens),
        ty => tokens.append_all(quote! { ::core::ffi::#ty }),
      },
      Self::Identifier { name, .. } => name.to_tokens(ctx, tokens),
      Self::Ptr { ty, mutable } => {
        let ty = ty.to_token_stream(ctx);

        tokens.append_all(if *mutable {
          quote! { *mut #ty }
        } else {
          quote! { *const #ty }
        })
      },
    }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

impl TryFrom<syn::Type> for Type {
  type Error = crate::Error;

  fn try_from(ty: syn::Type) -> Result<Self, Self::Error> {
    match ty {
      syn::Type::Ptr(ptr_ty) => {
        Ok(Self::Ptr { ty: Box::new(Self::try_from(*ptr_ty.elem)?), mutable: ptr_ty.mutability.is_some() })
      },
      syn::Type::Tuple(tuple_ty) if tuple_ty.elems.is_empty() => Ok(Type::BuiltIn(BuiltInType::Void)),
      syn::Type::Verbatim(ty) => Ok(Self::Identifier { name: Identifier::Literal(ty.to_string()), is_struct: false }),
      syn::Type::Path(path_ty) => {
        Ok(Self::Identifier { name: Identifier::Literal(path_ty.to_token_stream().to_string()), is_struct: false })
      },
      _ => Err(crate::Error::ParserError),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! ty {
    (*mut $($ty:tt)*) => { Type::Ptr { ty: Box::new(ty!($($ty)*)), mutable: true } };
    (*const $($ty:tt)*) => { Type::Ptr { ty: Box::new(ty!($($ty)*)), mutable: false } };
    (struct $ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).to_owned()), is_struct: true } };
    ($ty:ident) => { Type::Identifier { name: Identifier::Literal(stringify!($ty).to_owned()), is_struct: false } };
    ($ty:path) => { Type::BuiltIn($ty) };
  }

  #[test]
  fn parse_builtin() {
    let (_, ty) = Type::parse(&["float"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Float));

    let (_, ty) = Type::parse(&["double"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Double));

    let (_, ty) = Type::parse(&["long", "double"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongDouble));

    let (_, ty) = Type::parse(&["bool"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Bool));

    let (_, ty) = Type::parse(&["char"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Char));

    let (_, ty) = Type::parse(&["short"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(&["int"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(&["long", "long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));

    let (_, ty) = Type::parse(&["void"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Void));
  }

  #[test]
  fn parse_identifier() {
    let (_, ty) = Type::parse(&["MyType"]).unwrap();
    assert_eq!(ty, ty!(MyType));

    let (_, ty) = Type::parse(&["struct", "MyType"]).unwrap();
    assert_eq!(ty, ty!(struct MyType));
  }

  #[test]
  fn parse_all_consuming() {
    let (_, ty) = Type::parse(&["int8_t"]).unwrap();
    assert_eq!(ty, ty!(int8_t));
  }

  #[test]
  fn parse_signed_builtin() {
    let (_, ty) = Type::parse(&["signed", "char"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::SChar));

    let (_, ty) = Type::parse(&["signed", "short"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(&["signed", "int"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["signed", "long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(&["signed", "long", "long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));
  }

  #[test]
  fn parse_unsigned_builtin() {
    let (_, ty) = Type::parse(&["unsigned", "char"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UChar));

    let (_, ty) = Type::parse(&["unsigned", "short"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UShort));

    let (_, ty) = Type::parse(&["unsigned", "int"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UInt));

    let (_, ty) = Type::parse(&["unsigned", "long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULong));

    let (_, ty) = Type::parse(&["unsigned", "long", "long"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULongLong));
  }

  #[test]
  fn parse_ptr() {
    let (_, ty) = Type::parse(&["void", "*"]).unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::Void));

    let (_, ty) = Type::parse(&["void", "*", "const"]).unwrap();
    assert_eq!(ty, ty!(*const BuiltInType::Void));

    let (_, ty) = Type::parse(&["void", "*", "const", "*"]).unwrap();
    assert_eq!(ty, ty!(*mut *const BuiltInType::Void));
  }

  #[test]
  fn parse_const() {
    let (_, ty) = Type::parse(&["const", "int"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["int", "const"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["const", "int", "const"]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["const", "int", "*", "const"]).unwrap();
    assert_eq!(ty, ty!(*const BuiltInType::Int));
  }
}
