use quote::quote;

use crate::{CodegenContext, LocalContext};

/// Quote the given type as a static reference, eliding the `'static` lifetime if the Rust target supports it.
pub(crate) fn quote_static_ref<C: CodegenContext>(
  ctx: &LocalContext<'_, '_, C>,
  ty: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
  if ctx.static_lifetime_elision {
    quote! { &#ty }
  } else {
    quote! { &'static #ty }
  }
}

/// Quote the given bytes array as a `c_char` pointer.
pub(crate) fn quote_c_char_ptr<C: CodegenContext>(
  ctx: &LocalContext<'_, '_, C>,
  bytes: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
  let ffi_prefix = ctx.ffi_prefix().into_iter();

  let reference_ty = quote_static_ref(ctx, quote! { [u8] });

  quote! {
    {
      const BYTES: #reference_ty = #bytes.as_bytes();
      BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
    }
  }
}
