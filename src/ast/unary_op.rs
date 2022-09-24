use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{BuiltInType, Type};
use crate::{CodegenContext, Expr, LocalContext};

/// A unary operation.
#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
  /// `expr++`
  PostInc(Expr),
  /// `expr--`
  PostDec(Expr),
  /// `++expr`
  Inc(Expr),
  /// `--expr`
  Dec(Expr),
  /// `+expr`
  Plus(Expr),
  /// `-expr`
  Minus(Expr),
  /// `!expr`
  Not(Expr),
  /// `~expr`
  Comp(Expr),
  /// `*expr`
  Deref(Expr),
  /// `&expr`
  AddrOf(Expr),
}

impl UnaryOp {
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    match self {
      Self::Inc(expr) => expr.finish(ctx),
      Self::Dec(expr) => expr.finish(ctx),
      Self::PostInc(expr) => expr.finish(ctx),
      Self::PostDec(expr) => expr.finish(ctx),
      Self::Not(expr) => {
        expr.finish(ctx)?;
        // TODO: Evaluate literal.
        Ok(Some(Type::BuiltIn(BuiltInType::Bool)))
      },
      Self::Comp(expr) => expr.finish(ctx),
      Self::Plus(expr) => expr.finish(ctx),
      Self::Minus(expr) => expr.finish(ctx),
      Self::Deref(expr) => {
        let ty = expr.finish(ctx)?;
        if let Some(Type::Ptr { ty, .. }) = ty {
          Ok(Some(*ty))
        } else {
          Ok(ty)
        }
      },
      Self::AddrOf(expr) => {
        let ty = expr.finish(ctx)?;
        Ok(ty.map(|t| Type::Ptr { ty: Box::new(t), mutable: true }))
      },
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Inc(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { { #expr += 1; #expr } }
      },
      Self::Dec(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { { #expr -= 1; #expr } }
      },
      Self::PostInc(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { { let prev = #expr; #expr += 1; prev } }
      },
      Self::PostDec(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { { let prev = #expr; #expr -= 1; prev } }
      },
      Self::Not(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { (#expr == Default::default()) }
      },
      Self::Comp(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { (!#expr) }
      },
      Self::Plus(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { (+#expr) }
      },
      Self::Minus(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { (-#expr) }
      },
      Self::Deref(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { (*#expr) }
      },
      Self::AddrOf(expr) => {
        let expr = expr.to_token_stream(ctx);
        quote! { ::core::ptr::addr_of_mut!(#expr) }
      },
    })
  }
}
