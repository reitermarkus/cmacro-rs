use quote::TokenStreamExt;
use quote::quote;
use nom::IResult;
use nom::multi::fold_many0;
use quote::ToTokens;

use super::*;

/// A built-in type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltInType {
  Float,
  Double,
  Bool,
  Char,
  SChar,
  UChar,
  Short,
  UShort,
  Int,
  UInt,
  Long,
  ULong,
  LongLong,
  ULongLong,
  Void,
}

impl ToTokens for BuiltInType {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Float => quote! { f32 },
      Self::Double => quote! { f64 },
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

fn int_ty<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], BuiltInType> {
  fn int_signedness<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {
    alt((keyword("unsigned"), keyword("signed")))(input)
  }

  fn int_longness<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {
    alt((keyword("short"), keyword("long")))(input)
  }

  alt((
    // [const] [(un)signed] long long [int]
    map(
      permutation((
        const_qualifier,
        opt(int_signedness),
        keyword("long"),
        keyword("long"),
        opt(keyword("int")),
      )),
      |(_, s, _, _, _)| {
        if matches!(s, Some("unsigned")) {
          BuiltInType::ULongLong
        } else {
          BuiltInType::LongLong
        }
      },
    ),
    // [const] [(un)signed] long/short [int]
    map(
      permutation((
        const_qualifier,
        opt(int_signedness),
        int_longness,
        opt(keyword("int")),
      )),
      |(_, s, i, _)| {
        match (s, i) {
          (Some("unsigned"), "short") => BuiltInType::UShort,
          (_, "short") => BuiltInType::Short,
          (Some("unsigned"), "long") => BuiltInType::ULong,
          (_, "long") => BuiltInType::Long,
          _ => unreachable!(),
        }
      },
    ),
    // [const] [(un)signed] char/int
    map(
      permutation((
        const_qualifier,
        opt(int_signedness),
        alt((keyword("char"), keyword("int"))),
      )),
      |(_, s, i)| {
        match (s, i) {
          (Some("unsigned"), "int") => BuiltInType::UInt,
          (_, "int") => BuiltInType::Int,
          (Some("unsigned"), "char") => BuiltInType::UChar,
          (Some("signed"), "char") => BuiltInType::SChar,
          (_, "char") => BuiltInType::Char,
          _ => unreachable!(),
        }
      },
    ),
  ))(input)
}

fn ty<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Type> {
  alt((
    // [const] float/double/bool/void
    map(
      permutation((
        const_qualifier,
        alt((
          keyword("float"),
          keyword("double"),
          keyword("bool"),
        ),
      ))),
      |(_, ty)| match ty {
        "float" => Type::BuiltIn(BuiltInType::Float),
        "double" => Type::BuiltIn(BuiltInType::Double),
        "bool" => Type::BuiltIn(BuiltInType::Bool),
        "void" => Type::BuiltIn(BuiltInType::Void),
        _ => unreachable!(),
      },
    ),
    map(int_ty, Type::BuiltIn),
    // [const] <identifier>
    map(
      permutation((const_qualifier, pair(opt(keyword("struct")), identifier))),
      |(_, (s, id))| Type::Identifier {
        name: Identifier::Literal(id.to_owned()), is_struct: s.is_some()
      },
    ),
  ))(input)
}

fn const_qualifier<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], bool> {
  fold_many0(
    keyword("const"),
    || false,
    |_, _| true,
  )(input)
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  BuiltIn(BuiltInType),
  Identifier { name: Identifier, is_struct: bool },
  Ptr { ty: Box<Self>, mutable: bool },
}

impl Type {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, ty) = delimited(
      const_qualifier, ty, const_qualifier,
    )(tokens)?;

    fold_many0(
      preceded(pair(token("*"), meta), const_qualifier),
      move || ty.clone(),
      |acc, is_const| Type::Ptr { ty: Box::new(acc), mutable: !is_const },
    )(tokens)
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    match self {
      Self::BuiltIn(_) => (),
      Self::Identifier { name, .. } => name.finish(ctx)?,
      Self::Ptr { ty, .. } => ty.finish(ctx)?,
    }

    Ok(())
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    match self {
      Self::BuiltIn(ty) => {
        match ty {
          BuiltInType::Float | BuiltInType::Double | BuiltInType::Bool => ty.to_tokens(tokens),
          ty => tokens.append_all(quote! { ::core::ffi::#ty })
        }
      },
      Self::Identifier { name, .. } => {
        name.to_tokens(ctx, tokens)
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

  pub(crate) fn to_token_stream(&self, ctx: &mut LocalContext) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}
