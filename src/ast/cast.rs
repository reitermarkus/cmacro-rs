use proc_macro2::{Literal, TokenStream};
use quote::{quote, TokenStreamExt};

use crate::{CodegenContext, LocalContext};

use super::{Associativity, Expr, Lit, LitInt, Type};

/// A cast expression.
///
/// ```c
/// #define CAST (unsigned short)123
/// #define CAST (int*)&var
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cast<'t> {
  /// A type.
  pub ty: Type<'t>,
  /// An expression.
  pub expr: Box<Expr<'t>>,
}

impl<'t> Cast<'t> {
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    (3, Associativity::Left)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.ty.finish(ctx)?;
    self.expr.finish(ctx)?;
    Ok(Some(self.ty.clone()))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    tokens.append_all(match (&self.ty, &*self.expr) {
      (Type::Qualified { ty, qualifier }, Expr::Literal(Lit::Int(LitInt { value: 0, .. })))
        if matches!(**ty, Type::Ptr { .. }) && qualifier.is_const() =>
      {
        let prefix = ctx.trait_prefix().into_iter();
        quote! { #(#prefix::)*ptr::null() }
      },
      (Type::Ptr { .. }, Expr::Literal(Lit::Int(LitInt { value: 0, .. }))) => {
        let prefix = ctx.trait_prefix().into_iter();
        quote! { #(#prefix::)*ptr::null_mut() }
      },
      (ty, expr) => {
        if ty.is_void() {
          let expr = expr.to_token_stream(ctx);
          quote! { { let _ = #expr; } }
        } else {
          let (prec, _) = self.precedence();
          let (expr_prec, _) = expr.precedence();

          let expr = match expr {
            // When casting a negative integer, we need to generate it with a suffix, since
            // directly casting to an unsigned integer (i.e. `-1 as u32`) doesn't work.
            // The same is true when casting a big number to a type which is too small,
            // so we output the number with the smallest possible explicit type.
            Expr::Literal(Lit::Int(LitInt { value, .. })) => {
              let expr = if *value < i64::MIN as i128 {
                Literal::i128_suffixed(*value)
              } else if *value < i32::MIN as i128 {
                Literal::i64_suffixed(*value as i64)
              } else if *value < i16::MIN as i128 {
                Literal::i32_suffixed(*value as i32)
              } else if *value < i8::MIN as i128 {
                Literal::i16_suffixed(*value as i16)
              } else if *value < 0 {
                Literal::i8_suffixed(*value as i8)
              } else if *value <= u8::MAX as i128 {
                Literal::u8_suffixed(*value as u8)
              } else if *value <= u16::MAX as i128 {
                Literal::u16_suffixed(*value as u16)
              } else if *value <= u32::MAX as i128 {
                Literal::u32_suffixed(*value as u32)
              } else if *value <= u64::MAX as i128 {
                Literal::u64_suffixed(*value as u64)
              } else {
                Literal::i128_suffixed(*value)
              };

              quote! { #expr }
            },
            _ => {
              let mut expr = expr.to_token_stream(ctx);
              if expr_prec > prec {
                expr = quote! { (#expr) };
              }
              expr
            },
          };

          let ty = ty.to_token_stream(ctx);
          quote! { #expr as #ty }
        }
      },
    })
  }
}
