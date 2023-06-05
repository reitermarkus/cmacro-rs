use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::{CodegenContext, LocalContext};

use super::{Expr, Type};

/// A ternary expression.
///
/// ```c
/// #define TERNARY_EXPR(cond) cond ? 1 : 2
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TernaryExpr<'t> {
  /// A boolean condition.
  pub condition: Box<Expr<'t>>,
  /// The if branch.
  pub if_branch: Box<Expr<'t>>,
  /// The else branch.
  pub else_branch: Box<Expr<'t>>,
}

impl<'t> TernaryExpr<'t> {
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.condition.finish_condition(ctx)?;

    let lhs_ty = self.if_branch.finish(ctx)?;
    let rhs_ty = self.else_branch.finish(ctx)?;

    if lhs_ty == rhs_ty {
      Ok(lhs_ty)
    } else {
      Ok(lhs_ty.xor(rhs_ty))
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let cond = self.condition.to_token_stream(ctx);
    let if_branch = self.if_branch.to_token_stream(ctx);
    let else_branch = self.else_branch.to_token_stream(ctx);

    tokens.append_all(quote! {
      if #cond {
        #if_branch
      } else {
        #else_branch
      }
    })
  }
}
