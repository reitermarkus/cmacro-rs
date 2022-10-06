use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{BuiltInType, Type};
use crate::{CodegenContext, Expr, LocalContext};

/// A unary expression operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  /// `expr++`
  PostInc,
  /// `expr--`
  PostDec,
  /// `++expr`
  Inc,
  /// `--expr`
  Dec,
  /// `+expr`
  Plus,
  /// `-expr`
  Minus,
  /// `!expr`
  Not,
  /// `~expr`
  Comp,
  /// `*expr`
  Deref,
  /// `&expr`
  AddrOf,
}

/// A unary expression.
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
  /// Expression operator.
  pub op: UnaryOp,
  /// Expression.
  pub expr: Expr,
}

impl UnaryExpr {
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    let ty = self.expr.finish(ctx)?;

    match self.op {
      UnaryOp::Not => Ok(Some(Type::BuiltIn(BuiltInType::Bool))),
      UnaryOp::Deref => {
        if let Some(Type::Ptr { ty, .. }) = ty {
          Ok(Some(*ty))
        } else {
          Ok(ty)
        }
      },
      UnaryOp::AddrOf => Ok(ty.map(|ty| Type::Ptr { ty: Box::new(ty), mutable: true })),
      _ => Ok(ty),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let mut expr = self.expr.to_token_stream(ctx);

    if matches!(self.expr, Expr::Cast { .. }) {
      expr = quote! { (#expr) };
    }

    tokens.append_all(match self.op {
      UnaryOp::Inc => {
        quote! { { #expr += 1; #expr } }
      },
      UnaryOp::Dec => {
        quote! { { #expr -= 1; #expr } }
      },
      UnaryOp::PostInc => {
        quote! { { let prev = #expr; #expr += 1; prev } }
      },
      UnaryOp::PostDec => {
        quote! { { let prev = #expr; #expr -= 1; prev } }
      },
      UnaryOp::Not => {
        quote! { !(#expr) }
      },
      UnaryOp::Comp => {
        quote! { (!#expr) }
      },
      UnaryOp::Plus => {
        quote! { (+#expr) }
      },
      UnaryOp::Minus => {
        quote! { (-#expr) }
      },
      UnaryOp::Deref => format!("*{}", expr).parse::<TokenStream>().unwrap(),
      UnaryOp::AddrOf => {
        let trait_prefix = ctx.num_prefix();
        quote! { #trait_prefix ptr::addr_of_mut!(#expr) }
      },
    })
  }
}
