use std::{fmt::Debug, str::FromStr};

use nom::{
  branch::{alt, permutation},
  combinator::{map, opt},
  multi::fold_many0,
  sequence::{delimited, pair, preceded, terminated},
  Compare, IResult, InputLength, InputTake, Slice,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};

use super::*;
use crate::{CodegenContext, LocalContext, ParseContext};

/// A built-in type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
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
  /// `char8_t`
  Char8T,
  /// `char16_t`
  Char16T,
  /// `char32_t`
  Char32T,
  /// (`signed`) `short`
  Short,
  /// `unsigned short`
  UShort,
  /// (`signed`) `int`
  Int,
  /// `unsigned int`
  UInt,
  /// (`signed`) `long`
  Long,
  /// `unsigned long`
  ULong,
  /// (`signed`) `long long`
  LongLong,
  /// `unsigned long long`
  ULongLong,
  /// `size_t`
  SizeT,
  /// `ssize_t`
  SSizeT,
  /// `void`
  Void,
}

impl BuiltInType {
  /// Return the suffix used for literals of this type.
  pub fn suffix(&self) -> Option<&'static str> {
    match self {
      Self::Float => Some("f"),
      Self::LongDouble => Some("l"),
      Self::UInt => Some("u"),
      Self::ULong => Some("ul"),
      Self::Long => Some("l"),
      Self::ULongLong => Some("ull"),
      Self::LongLong => Some("ll"),
      Self::SizeT => Some("uz"),
      Self::SSizeT => Some("z"),
      _ => None,
    }
  }

  fn to_rust_ty(self, ffi_prefix: Option<syn::Path>) -> syn::Type {
    let ffi_prefix = ffi_prefix.into_iter();

    match self {
      Self::Float => syn::parse_quote! { f32 },
      Self::Double | Self::LongDouble => syn::parse_quote! { f64 },
      Self::Bool => syn::parse_quote! { bool },
      Self::Char => syn::parse_quote! { #(#ffi_prefix::)*c_char },
      Self::SChar => syn::parse_quote! { #(#ffi_prefix::)*c_schar },
      Self::UChar => syn::parse_quote! { #(#ffi_prefix::)*c_uchar },
      Self::Char8T => syn::parse_quote! { u8 },
      Self::Char16T => syn::parse_quote! { u16 },
      Self::Char32T => syn::parse_quote! { u32 },
      Self::Short => syn::parse_quote! { #(#ffi_prefix::)*c_short },
      Self::UShort => syn::parse_quote! { #(#ffi_prefix::)*c_ushort },
      Self::Int => syn::parse_quote! { #(#ffi_prefix::)*c_int },
      Self::UInt => syn::parse_quote! { #(#ffi_prefix::)*c_uint },
      Self::Long => syn::parse_quote! { #(#ffi_prefix::)*c_long },
      Self::ULong => syn::parse_quote! { #(#ffi_prefix::)*c_ulong },
      Self::LongLong => syn::parse_quote! { #(#ffi_prefix::)*c_longlong },
      Self::ULongLong => syn::parse_quote! { #(#ffi_prefix::)*c_ulonglong },
      Self::SizeT => syn::parse_quote! { #(#ffi_prefix::)*size_t },
      Self::SSizeT => syn::parse_quote! { #(#ffi_prefix::)*ssize_t },
      Self::Void => syn::parse_quote! { #(#ffi_prefix::)*c_void },
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let ffi_prefix = ctx.ffi_prefix();
    self.to_rust_ty(ffi_prefix).to_tokens(tokens);
  }
}

fn int_ty<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], BuiltInType> {
  fn int_signedness<I>(input: &[I]) -> IResult<&[I], &'static str>
  where
    I: Debug + InputTake + InputLength + Slice<std::ops::RangeFrom<usize>> + Compare<&'static str> + Clone,
  {
    alt((keyword("unsigned"), keyword("signed")))(input)
  }

  fn int_length<I>(input: &[I]) -> IResult<&[I], &'static str>
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
    map(permutation((const_qualifier, opt(int_signedness), int_length, opt(keyword("int")))), |(_, s, i, _)| {
      match (s, i) {
        (Some("unsigned"), "short") => BuiltInType::UShort,
        (_, "short") => BuiltInType::Short,
        (Some("unsigned"), "long") => BuiltInType::ULong,
        (_, "long") => BuiltInType::Long,
        _ => unreachable!(),
      }
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

fn ty<'i, 't>(input: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Type> {
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
    map(
      delimited(
        const_qualifier,
        pair(opt(keyword("struct")), |tokens| Expr::parse_concat_ident(tokens, ctx)),
        const_qualifier,
      ),
      |(s, id)| Type::Identifier { name: Box::new(id), is_struct: s.is_some() },
    ),
  ))(input)
}

fn const_qualifier<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], bool> {
  fold_many0(keyword("const"), || false, |_, _| true)(input)
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  /// A built-in type.
  BuiltIn(BuiltInType),
  /// A type identifier.
  #[allow(missing_docs)]
  Identifier { name: Box<Expr>, is_struct: bool },
  /// A type path.
  #[allow(missing_docs)]
  Path { leading_colon: bool, segments: Vec<LitIdent> },
  /// A pointer type.
  #[allow(missing_docs)]
  Ptr { ty: Box<Self>, mutable: bool },
}

impl Type {
  /// Parse a type.
  pub(crate) fn parse<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, ty) = delimited(const_qualifier, |tokens| ty(tokens, ctx), const_qualifier)(tokens)?;

    fold_many0(
      preceded(pair(token("*"), meta), const_qualifier),
      move || ty.clone(),
      |acc, is_const| Type::Ptr { ty: Box::new(acc), mutable: !is_const },
    )(tokens)
  }

  /// Check if this type is `void`.
  pub fn is_void(&self) -> bool {
    matches!(self, Self::BuiltIn(BuiltInType::Void))
  }

  /// Check if this is a pointer type.
  pub fn is_ptr(&self) -> bool {
    matches!(self, Self::Ptr { .. })
  }

  pub(crate) fn from_resolved_type(resolved_type: &str) -> Self {
    match resolved_type {
      "float" => Type::BuiltIn(BuiltInType::Float),
      "double" => Type::BuiltIn(BuiltInType::Double),
      "long double" => Type::BuiltIn(BuiltInType::LongDouble),
      "bool" => Type::BuiltIn(BuiltInType::Bool),
      "char" => Type::BuiltIn(BuiltInType::Char),
      "signed char" => Type::BuiltIn(BuiltInType::SChar),
      "unsigned char" => Type::BuiltIn(BuiltInType::UChar),
      "char8_t" => Type::BuiltIn(BuiltInType::Char8T),
      "char16_t" => Type::BuiltIn(BuiltInType::Char16T),
      "char32_t" => Type::BuiltIn(BuiltInType::Char32T),
      "short" => Type::BuiltIn(BuiltInType::Short),
      "unsigned short" => Type::BuiltIn(BuiltInType::UShort),
      "int" => Type::BuiltIn(BuiltInType::Int),
      "unsigned int" => Type::BuiltIn(BuiltInType::UInt),
      "long" => Type::BuiltIn(BuiltInType::Long),
      "unsigned long" => Type::BuiltIn(BuiltInType::ULong),
      "long long" => Type::BuiltIn(BuiltInType::LongLong),
      "unsigned long long" => Type::BuiltIn(BuiltInType::ULongLong),
      "void" => Type::BuiltIn(BuiltInType::Void),
      ty => {
        Type::Identifier { name: Box::new(Expr::Variable { name: LitIdent { id: ty.to_owned() } }), is_struct: false }
      },
    }
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::BuiltIn(_) => Ok(None),
      Self::Identifier { name, .. } => {
        name.finish(ctx)?;

        if let Expr::Arg { name: ref id } = **name {
          if let Some(ty) = ctx.resolve_ty(id.as_str()) {
            *self = Self::from_resolved_type(&ty);
          }
        }

        Ok(None)
      },
      Self::Path { .. } => Ok(None),
      Self::Ptr { ty, .. } => ty.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::BuiltIn(ty) => ty.to_tokens(ctx, tokens),
      Self::Identifier { name, .. } => name.to_tokens(ctx, tokens),
      Self::Path { segments, leading_colon } => {
        let leading_colon = if *leading_colon { Some(quote! { :: }) } else { None };
        let ids = segments.iter().map(|id| Ident::new(id.as_str(), Span::call_site()));
        tokens.append_all(quote! { #leading_colon #(#ids)::* })
      },
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

impl FromStr for Type {
  type Err = crate::CodegenError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    // Pointer star needs to be a separate token.
    let ty = s.replace('*', " * ");

    let tokens = ty.split_whitespace().collect::<Vec<_>>();
    let ctx = ParseContext { name: "", args: &[] };
    let (_, ty) = Self::parse(&tokens, &ctx).map_err(|_| crate::CodegenError::UnsupportedType(s.to_owned()))?;
    Ok(ty)
  }
}

impl TryFrom<syn::Type> for Type {
  type Error = crate::CodegenError;

  fn try_from(ty: syn::Type) -> Result<Self, Self::Error> {
    match ty {
      syn::Type::Ptr(ptr_ty) => {
        Ok(Self::Ptr { ty: Box::new(Self::try_from(*ptr_ty.elem)?), mutable: ptr_ty.mutability.is_some() })
      },
      syn::Type::Tuple(tuple_ty) if tuple_ty.elems.is_empty() => Ok(Type::BuiltIn(BuiltInType::Void)),
      syn::Type::Verbatim(ty) => Ok(Self::Identifier {
        name: Box::new(Expr::Variable { name: LitIdent { id: ty.to_string() } }),
        is_struct: false,
      }),
      syn::Type::Path(path_ty) => Ok(Self::Path {
        leading_colon: path_ty.path.leading_colon.is_some(),
        segments: path_ty.path.segments.iter().map(|s| LitIdent { id: s.ident.to_string() }).collect(),
      }),
      ty => Err(crate::CodegenError::UnsupportedType(ty.into_token_stream().to_string())),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const CTX: ParseContext = ParseContext::var_macro("IDENTIFIER");

  #[test]
  fn parse_builtin() {
    let (_, ty) = Type::parse(&["float"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Float));

    let (_, ty) = Type::parse(&["double"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Double));

    let (_, ty) = Type::parse(&["long", "double"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongDouble));

    let (_, ty) = Type::parse(&["bool"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Bool));

    let (_, ty) = Type::parse(&["char"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Char));

    let (_, ty) = Type::parse(&["short"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(&["int"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(&["long", "long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));

    let (_, ty) = Type::parse(&["void"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Void));
  }

  #[test]
  fn parse_identifier() {
    let (_, ty) = Type::parse(&["MyType"], &CTX).unwrap();
    assert_eq!(ty, ty!(MyType));

    let (_, ty) = Type::parse(&["struct", "MyType"], &CTX).unwrap();
    assert_eq!(ty, ty!(struct MyType));
  }

  #[test]
  fn parse_all_consuming() {
    let (_, ty) = Type::parse(&["int8_t"], &CTX).unwrap();
    assert_eq!(ty, ty!(int8_t));
  }

  #[test]
  fn parse_signed_builtin() {
    let (_, ty) = Type::parse(&["signed", "char"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::SChar));

    let (_, ty) = Type::parse(&["signed", "short"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(&["signed", "int"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["signed", "long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(&["signed", "long", "long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));
  }

  #[test]
  fn parse_unsigned_builtin() {
    let (_, ty) = Type::parse(&["unsigned", "char"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UChar));

    let (_, ty) = Type::parse(&["unsigned", "short"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UShort));

    let (_, ty) = Type::parse(&["unsigned", "int"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UInt));

    let (_, ty) = Type::parse(&["unsigned", "long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULong));

    let (_, ty) = Type::parse(&["unsigned", "long", "long"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULongLong));
  }

  #[test]
  fn parse_ptr() {
    let (_, ty) = Type::parse(&["void", "*"], &CTX).unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::Void));

    let (_, ty) = Type::parse(&["void", "*", "const"], &CTX).unwrap();
    assert_eq!(ty, ty!(*const BuiltInType::Void));

    let (_, ty) = Type::parse(&["void", "*", "const", "*"], &CTX).unwrap();
    assert_eq!(ty, ty!(*mut *const BuiltInType::Void));
  }

  #[test]
  fn parse_const() {
    let (_, ty) = Type::parse(&["const", "int"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["int", "const"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["const", "int", "const"], &CTX).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(&["const", "int", "*", "const"], &CTX).unwrap();
    assert_eq!(ty, ty!(*const BuiltInType::Int));
  }

  #[test]
  fn from_str() {
    let ty = "unsigned int".parse::<Type>().unwrap();
    assert_eq!(ty, ty!(BuiltInType::UInt));

    let ty = "unsigned int*".parse::<Type>().unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::UInt));

    let ty = "char *".parse::<Type>().unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::Char));
  }
}
