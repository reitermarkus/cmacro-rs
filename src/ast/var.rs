use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::{codegen::quote_c_char_ptr, CodegenContext, LocalContext, MacroArgType};

use super::{BuiltInType, IdentifierExpr, Type, TypeQualifier};

/// A variable.
///
/// ```c
/// #define VAR abc
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Var<'t> {
  pub(crate) name: IdentifierExpr<'t>,
}

impl<'t> Var<'t> {
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.name.finish(ctx)?;

    match &self.name {
      IdentifierExpr::Arg(arg) => {
        if let MacroArgType::Known(arg_ty) = ctx.arg_type_mut(arg.index()) {
          Ok(Some(arg_ty.clone()))
        } else {
          Ok(None)
        }
      },
      IdentifierExpr::Plain(id) => {
        // Built-in macros.
        match id.as_str() {
          "__LINE__" => {
            ctx.export_as_macro = true;
            Ok(Some(Type::BuiltIn(BuiltInType::UInt)))
          },
          "__FILE__" => {
            ctx.export_as_macro = true;
            Ok(Some(Type::Qualified {
              ty: Box::new(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)) }),
              qualifier: TypeQualifier::Const,
            }))
          },
          "__SCHAR_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::SChar))),
          "__SHRT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Short))),
          "__INT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Int))),
          "__LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Long))),
          "__LONG_LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::LongLong))),
          name => {
            if let Some((enum_ty, _)) = ctx.resolve_enum_variant(name) {
              Ok(Some(Type::from_rust_ty(&enum_ty, ctx.ffi_prefix().as_ref())?))
            } else {
              // Variable is not defined, so we need to export this as a macro.
              ctx.export_as_macro = true;
              Ok(None)
            }
          },
        }
      },
      IdentifierExpr::Concat(_) => Ok(None),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let ffi_prefix = ctx.ffi_prefix().into_iter();

    if let IdentifierExpr::Plain(ref name) = self.name {
      tokens.append_all(match name.as_str() {
        "__LINE__" => {
          let trait_prefix = ctx.trait_prefix().into_iter();
          quote! { #(#trait_prefix::)*line!() as #(#ffi_prefix::)*c_uint }
        },
        "__FILE__" => {
          let file = {
            let trait_prefix = ctx.trait_prefix().into_iter();
            quote! { #(#trait_prefix::)*file!() }
          };

          let trait_prefix = ctx.trait_prefix().into_iter();
          quote_c_char_ptr(ctx, quote! { #(#trait_prefix::)*concat!(#file, '\0') })
        },
        "__SCHAR_MAX__" => quote! { #(#ffi_prefix::)*c_schar::MAX },
        "__SHRT_MAX__" => quote! { #(#ffi_prefix::)*c_short::MAX },
        "__INT_MAX__" => quote! { #(#ffi_prefix::)*c_int::MAX },
        "__LONG_MAX__" => quote! { #(#ffi_prefix::)*c_long::MAX },
        "__LONG_LONG_MAX__" => quote! { #(#ffi_prefix::)*c_longlong::MAX },
        name => {
          if let Some((_, enum_variant)) = ctx.resolve_enum_variant(name) {
            quote! { #enum_variant }
          } else {
            self.name.to_token_stream(ctx)
          }
        },
      })
    } else {
      self.name.to_tokens(ctx, tokens)
    }
  }
}
