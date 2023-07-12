use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use crate::{CodegenContext, LocalContext};

use super::{BuiltInType, Identifier, Type, TypeQualifier};

/// A variable.
///
/// ```c
/// #define VAR abc
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Var<'t> {
  pub(crate) name: Identifier<'t>,
}

impl<'t> Var<'t> {
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    // Built-in macros.
    match self.name.as_str() {
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
      _ => Ok(None),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let ffi_prefix = ctx.ffi_prefix().into_iter();

    tokens.append_all(match self.name.as_str() {
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
        quote! {
          {
            const BYTES: &[u8] = #(#trait_prefix::)*concat!(#file, '\0').as_bytes();
            BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
          }
        }
      },
      "__SCHAR_MAX__" => quote! { #(#ffi_prefix::)*c_schar::MAX },
      "__SHRT_MAX__" => quote! { #(#ffi_prefix::)*c_short::MAX },
      "__INT_MAX__" => quote! { #(#ffi_prefix::)*c_int::MAX },
      "__LONG_MAX__" => quote! { #(#ffi_prefix::)*c_long::MAX },
      "__LONG_LONG_MAX__" => quote! { #(#ffi_prefix::)*c_longlong::MAX },
      name => {
        if let Some(enum_variant) = ctx.resolve_enum_variant(name) {
          quote! { #enum_variant }
        } else {
          let name = Ident::new(name, Span::call_site());
          quote! { #name }
        }
      },
    })
  }
}
