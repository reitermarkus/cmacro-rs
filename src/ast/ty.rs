use std::{borrow::Cow, fmt::Debug, str::FromStr};

use nom::{
  branch::{alt, permutation},
  combinator::{map, opt},
  multi::fold_many0,
  sequence::{delimited, pair, preceded, terminated},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};

use super::*;
use crate::{CodegenContext, LocalContext, MacroToken};

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

  fn from_rust_ty(ty: &syn::TypePath, ffi_prefix: Option<&syn::Path>) -> Option<Self> {
    match ty {
      syn::TypePath { qself: None, path: syn::Path { leading_colon, segments } } => {
        let mut it = segments.iter();

        if let Some(ffi_prefix) = ffi_prefix {
          if leading_colon.is_some() != ffi_prefix.leading_colon.is_some() {
            return None
          }

          for segment in ffi_prefix.segments.iter() {
            if it.next()?.ident != segment.ident {
              return None
            }
          }
        }

        let id = &it.next()?.ident;

        // ID must be the last segment.
        if it.next().is_some() {
          return None
        }

        Some(if id == "f32" {
          Self::Float
        } else if id == "f64" {
          Self::Double
        } else if id == "f128" {
          Self::LongDouble
        } else if id == "bool" {
          Self::Bool
        } else if id == "c_char" {
          Self::Char
        } else if id == "c_schar" {
          Self::SChar
        } else if id == "c_uchar" {
          Self::UChar
        } else if id == "u8" {
          Self::Char8T
        } else if id == "u16" {
          Self::Char16T
        } else if id == "u32" {
          Self::Char32T
        } else if id == "c_short" {
          Self::Short
        } else if id == "c_ushort" {
          Self::UShort
        } else if id == "c_int" {
          Self::Int
        } else if id == "c_uint" {
          Self::UInt
        } else if id == "c_long" {
          Self::Long
        } else if id == "c_ulong" {
          Self::ULong
        } else if id == "c_longlong" {
          Self::LongLong
        } else if id == "c_ulonglong" {
          Self::ULongLong
        } else if id == "size_t" {
          Self::SizeT
        } else if id == "ssize_t" {
          Self::SSizeT
        } else if id == "c_void" {
          Self::Void
        } else {
          return None
        })
      },
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

  pub(crate) fn to_tokens<C: CodegenContext>(self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    let ffi_prefix = ctx.ffi_prefix();
    self.to_rust_ty(ffi_prefix).to_tokens(tokens);
  }
}

fn int_ty<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], BuiltInType> {
  fn int_signedness<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str> {
    alt((keyword("unsigned"), keyword("signed")))(input)
  }

  fn int_length<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str> {
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

fn ty<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Type<'t>> {
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
      delimited(const_qualifier, pair(opt(keyword("struct")), Expr::parse_concat_ident), const_qualifier),
      |(s, id)| Type::Identifier { name: Box::new(id), is_struct: s.is_some() },
    ),
  ))(input)
}

fn const_qualifier<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], bool> {
  fold_many0(keyword("const"), || false, |_, _| true)(input)
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type<'t> {
  /// A built-in type.
  BuiltIn(BuiltInType),
  /// A type identifier.
  #[allow(missing_docs)]
  Identifier { name: Box<Expr<'t>>, is_struct: bool },
  /// A type path.
  #[allow(missing_docs)]
  Path { leading_colon: bool, segments: Vec<Identifier<'t>> },
  /// A pointer type.
  #[allow(missing_docs)]
  Ptr { ty: Box<Self>, mutable: bool },
}

impl<'t> Type<'t> {
  /// Parse a type.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, ty) = delimited(const_qualifier, ty, const_qualifier)(tokens)?;

    fold_many0(
      preceded(pair(punct("*"), meta), const_qualifier),
      move || ty.clone(),
      |acc, is_const| Self::Ptr { ty: Box::new(acc), mutable: !is_const },
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

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::BuiltIn(_) => Ok(None),
      Self::Identifier { name, .. } => {
        name.finish(ctx)?;

        if let Expr::Variable { name: ref id } = **name {
          if let Some(ty) = ctx.resolve_ty(id.as_str()) {
            *self = Self::from_rust_ty(&ty, ctx.ffi_prefix().as_ref())?;
          }
        }

        Ok(None)
      },
      Self::Path { .. } => Ok(None),
      Self::Ptr { ty, .. } => ty.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
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

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }

  pub(crate) fn from_rust_ty(ty: &syn::Type, ffi_prefix: Option<&syn::Path>) -> Result<Self, crate::CodegenError> {
    match ty {
      syn::Type::Ptr(ptr_ty) => Ok(Self::Ptr {
        ty: Box::new(Self::from_rust_ty(&ptr_ty.elem, ffi_prefix)?),
        mutable: ptr_ty.mutability.is_some(),
      }),
      syn::Type::Tuple(tuple_ty) if tuple_ty.elems.is_empty() => Ok(Type::BuiltIn(BuiltInType::Void)),
      syn::Type::Verbatim(ty) => Ok(Self::Identifier {
        name: Box::new(Expr::Variable { name: Identifier { id: ty.to_string().into() } }),
        is_struct: false,
      }),
      syn::Type::Path(path_ty) => {
        if let Some(ty) = BuiltInType::from_rust_ty(path_ty, ffi_prefix) {
          return Ok(Self::BuiltIn(ty))
        }

        Ok(Self::Path {
          leading_colon: path_ty.path.leading_colon.is_some(),
          segments: path_ty.path.segments.iter().map(|s| Identifier { id: s.ident.to_string().into() }).collect(),
        })
      },
      ty => Err(crate::CodegenError::UnsupportedType(ty.into_token_stream().to_string())),
    }
  }

  // Only used for tests.
  #[doc(hidden)]
  pub fn to_rust_ty(&self, ffi_prefix: Option<syn::Path>) -> Option<syn::Type> {
    Some(match self {
      Self::BuiltIn(ty) => ty.to_rust_ty(ffi_prefix),
      Self::Identifier { name, .. } => {
        if let Expr::Variable { name } = &**name {
          let name = Ident::new(name.as_str(), Span::call_site());
          syn::parse_quote! { #name }
        } else {
          return None
        }
      },
      Self::Path { leading_colon, segments } => {
        let colon = if *leading_colon { Some(quote! { :: }) } else { None }.into_iter();

        let segments = segments.iter().map(|s| Ident::new(s.as_str(), Span::call_site()));

        syn::parse_quote! { #(#colon)* #(#segments)::*  }
      },
      Self::Ptr { ty, mutable } => {
        let constness = if *mutable {
          quote! { *mut }
        } else {
          quote! { *const }
        };

        let ty = ty.to_rust_ty(ffi_prefix)?;
        syn::parse_quote! { #constness #ty }
      },
    })
  }

  pub(crate) fn to_static(&self) -> Option<Type<'static>> {
    match self {
      Self::BuiltIn(ty) => Some(Type::BuiltIn(*ty)),
      Self::Identifier { name, is_struct } => {
        if let Expr::Variable { name } = &**name {
          Some(Type::Identifier { name: Box::new(Expr::Variable { name: name.to_static() }), is_struct: *is_struct })
        } else {
          // TODO: Implement `to_static` for `Expr`.
          None
        }
      },
      Self::Path { leading_colon, segments } => {
        Some(Type::Path { leading_colon: *leading_colon, segments: segments.iter().map(|ty| ty.to_static()).collect() })
      },
      Self::Ptr { ty, mutable } => Some(Type::Ptr { ty: Box::new(ty.to_static()?), mutable: *mutable }),
    }
  }
}

impl FromStr for Type<'static> {
  type Err = crate::CodegenError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    // Pointer star needs to be a separate token.
    let ty = s.replace('*', " * ");

    let tokens = ty
      .split_whitespace()
      .map(|t| {
        if let Ok(identifier) = Identifier::try_from(t) {
          MacroToken::Identifier(identifier)
        } else if let Ok(p) = Punctuation::try_from(t) {
          MacroToken::Punctuation(p)
        } else {
          MacroToken::Token(Cow::Borrowed(t))
        }
      })
      .collect::<Vec<_>>();
    let (_, ty) = Type::parse(&tokens).map_err(|_| crate::CodegenError::UnsupportedType(s.to_owned()))?;

    match ty.to_static() {
      Some(ty) => Ok(ty),
      _ => Err(crate::CodegenError::UnsupportedType(s.to_owned())),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_token::{id as macro_id, punct as macro_punct, tokens};

  #[test]
  fn parse_builtin_from_syn_type() {
    let no_prefix = None;
    let core_ffi_prefix = Some(syn::parse_quote! { ::core::ffi });
    let std_ffi_prefix = Some(syn::parse_quote! { ::std::ffi });

    let ty: syn::TypePath = syn::parse_quote! { c_int };
    assert_eq!(BuiltInType::from_rust_ty(&ty, no_prefix.as_ref()), Some(BuiltInType::Int));
    assert_eq!(BuiltInType::from_rust_ty(&ty, core_ffi_prefix.as_ref()), None);
    assert_eq!(BuiltInType::from_rust_ty(&ty, std_ffi_prefix.as_ref()), None);

    let ty: syn::TypePath = syn::parse_quote! { ::c_int };
    assert_eq!(BuiltInType::from_rust_ty(&ty, no_prefix.as_ref()), Some(BuiltInType::Int));
    assert_eq!(BuiltInType::from_rust_ty(&ty, core_ffi_prefix.as_ref()), None);
    assert_eq!(BuiltInType::from_rust_ty(&ty, std_ffi_prefix.as_ref()), None);

    let ty: syn::TypePath = syn::parse_quote! { ::core::ffi::c_int };
    assert_eq!(BuiltInType::from_rust_ty(&ty, no_prefix.as_ref()), None);
    assert_eq!(BuiltInType::from_rust_ty(&ty, core_ffi_prefix.as_ref()), Some(BuiltInType::Int));
    assert_eq!(BuiltInType::from_rust_ty(&ty, std_ffi_prefix.as_ref()), None);

    let ty: syn::TypePath = syn::parse_quote! { ::std::ffi::c_int };
    assert_eq!(BuiltInType::from_rust_ty(&ty, no_prefix.as_ref()), None);
    assert_eq!(BuiltInType::from_rust_ty(&ty, core_ffi_prefix.as_ref()), None);
    assert_eq!(BuiltInType::from_rust_ty(&ty, std_ffi_prefix.as_ref()), Some(BuiltInType::Int));
  }

  #[test]
  fn parse_builtin() {
    let (_, ty) = Type::parse(tokens![macro_id!(float)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Float));

    let (_, ty) = Type::parse(tokens![macro_id!(double)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Double));

    let (_, ty) = Type::parse(tokens![macro_id!(long), macro_id!(double)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongDouble));

    let (_, ty) = Type::parse(tokens![macro_id!(bool)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Bool));

    let (_, ty) = Type::parse(tokens![macro_id!(char)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Char));

    let (_, ty) = Type::parse(tokens![macro_id!(short)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(tokens![macro_id!(int)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(tokens![macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(tokens![macro_id!(long), macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));

    let (_, ty) = Type::parse(tokens![macro_id!(void)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Void));
  }

  #[test]
  fn parse_identifier() {
    let (_, ty) = Type::parse(tokens![macro_id!(MyType)]).unwrap();
    assert_eq!(ty, ty!(MyType));

    let (_, ty) = Type::parse(tokens![macro_id!(struct), macro_id!(MyType)]).unwrap();
    assert_eq!(ty, ty!(struct MyType));
  }

  #[test]
  fn parse_all_consuming() {
    let (_, ty) = Type::parse(tokens![macro_id!(int8_t)]).unwrap();
    assert_eq!(ty, ty!(int8_t));
  }

  #[test]
  fn parse_signed_builtin() {
    let (_, ty) = Type::parse(tokens![macro_id!(signed), macro_id!(char)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::SChar));

    let (_, ty) = Type::parse(tokens![macro_id!(signed), macro_id!(short)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Short));

    let (_, ty) = Type::parse(tokens![macro_id!(signed), macro_id!(int)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(tokens![macro_id!(signed), macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Long));

    let (_, ty) = Type::parse(tokens![macro_id!(signed), macro_id!(long), macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::LongLong));
  }

  #[test]
  fn parse_unsigned_builtin() {
    let (_, ty) = Type::parse(tokens![macro_id!(unsigned), macro_id!(char)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UChar));

    let (_, ty) = Type::parse(tokens![macro_id!(unsigned), macro_id!(short)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UShort));

    let (_, ty) = Type::parse(tokens![macro_id!(unsigned), macro_id!(int)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::UInt));

    let (_, ty) = Type::parse(tokens![macro_id!(unsigned), macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULong));

    let (_, ty) = Type::parse(tokens![macro_id!(unsigned), macro_id!(long), macro_id!(long)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::ULongLong));
  }

  #[test]
  fn parse_ptr() {
    let (_, ty) = Type::parse(tokens![macro_id!(void), macro_punct!("*")]).unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::Void));

    let (_, ty) = Type::parse(tokens![macro_id!(void), macro_punct!("*"), macro_id!(const)]).unwrap();
    assert_eq!(ty, ty!(*const BuiltInType::Void));

    let (_, ty) =
      Type::parse(tokens![macro_id!(void), macro_punct!("*"), macro_id!(const), macro_punct!("*")]).unwrap();
    assert_eq!(ty, ty!(*mut *const BuiltInType::Void));
  }

  #[test]
  fn parse_const() {
    let (_, ty) = Type::parse(tokens![macro_id!(const), macro_id!(int)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(tokens![macro_id!(int), macro_id!(const)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(tokens![macro_id!(const), macro_id!(int), macro_id!(const)]).unwrap();
    assert_eq!(ty, ty!(BuiltInType::Int));

    let (_, ty) = Type::parse(tokens![macro_id!(const), macro_id!(int), macro_punct!("*"), macro_id!(const)]).unwrap();
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

    let ty = "char*".parse::<Type>().unwrap();
    assert_eq!(ty, ty!(*mut BuiltInType::Char));
  }
}
