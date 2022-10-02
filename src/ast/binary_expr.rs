use std::fmt::Debug;

use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use super::{BuiltInType, Identifier, Lit, LitFloat, LitInt, Type};
use crate::{CodegenContext, Expr, LocalContext};

/// A binary expression operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
  /// lhs * rhs
  Mul,
  /// lhs / rhs
  Div,
  /// lhs % rhs
  Rem,
  /// lhs + rhs
  Add,
  /// lhs - rhs
  Sub,
  /// lhs << rhs
  Shl,
  /// lhs >> rhs
  Shr,
  /// lhs < rhs
  Lt,
  /// lhs <= rhs
  Lte,
  /// lhs > rhs
  Gt,
  /// lhs >= rhs
  Gte,
  /// lhs == rhs
  Eq,
  /// lhs != rhs
  Neq,
  /// lhs & rhs
  BitAnd,
  /// lhs ^ rhs
  BitXor,
  /// lhs | rhs
  BitOr,
  /// lhs && rhs
  And,
  /// lhs || rhs
  Or,
  /// lhs = rhs
  Assign,
  /// lhs += rhs
  AddAssign,
  /// lhs -= rhs
  SubAssign,
  /// lhs *= rhs
  MulAssign,
  /// lhs /= rhs
  DivAssign,
  /// lhs %= rhs
  RemAssign,
  /// lhs <<= rhs
  ShlAssign,
  /// lhs >>= rhs
  ShrAssign,
  /// lhs &= rhs
  BitAndAssign,
  /// lhs ^= rhs
  BitXorAssign,
  /// lhs |= rhs
  BitOrAssign,
}

impl ToTokens for BinaryOp {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Mul => quote! { * },
      Self::Div => quote! { / },
      Self::Rem => quote! { % },
      Self::Add => quote! { + },
      Self::Sub => quote! { - },
      Self::Shl => quote! { << },
      Self::Shr => quote! { >> },
      Self::Lt => quote! { < },
      Self::Lte => quote! { <= },
      Self::Gt => quote! { > },
      Self::Gte => quote! { >= },
      Self::Eq => quote! { == },
      Self::Neq => quote! { != },
      Self::BitAnd => quote! { & },
      Self::BitXor => quote! { ^ },
      Self::BitOr => quote! { | },
      Self::And => quote! { && },
      Self::Or => quote! { || },
      Self::Assign => quote! { =  },
      Self::AddAssign => quote! { += },
      Self::SubAssign => quote! { -= },
      Self::MulAssign => quote! { *= },
      Self::DivAssign => quote! { /= },
      Self::RemAssign => quote! { %= },
      Self::ShlAssign => quote! { <<= },
      Self::ShrAssign => quote! { >>= },
      Self::BitAndAssign => quote! { &= },
      Self::BitXorAssign => quote! { ^= },
      Self::BitOrAssign => quote! { |= },
    })
  }
}

/// A binary expression.
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
  /// Left-hand side expression.
  pub lhs: Expr,
  /// Expression operator.
  pub op: BinaryOp,
  /// Right-hand side expression.
  pub rhs: Expr,
}

impl BinaryExpr {
  pub(crate) fn finish<'g, C>(
    &mut self,
    ctx: &mut LocalContext<'g, C>,
  ) -> Result<(Option<Type>, Option<Type>), crate::Error>
  where
    C: CodegenContext,
  {
    let max_ty_cast = |expr: &Expr| {
      if let Expr::Variable { name: Identifier::Literal(id) } = expr {
        return Some(Type::BuiltIn(match id.as_str() {
          "__SCHAR_MAX__" => BuiltInType::UChar,
          "__SHRT_MAX__" => BuiltInType::UShort,
          "__INT_MAX__" => BuiltInType::UInt,
          "__LONG_MAX__" => BuiltInType::ULong,
          "__LONG_LONG_MAX__" => BuiltInType::ULongLong,
          _ => return None,
        }))
      }

      None
    };

    // Cast mixed float and int expression.
    match (&self.lhs, &self.rhs) {
      (Expr::Literal(Lit::Int(LitInt { value: lhs, suffix: None })), Expr::Literal(Lit::Float(_))) => {
        let f = if *lhs >= f32::MIN as i128 && *lhs <= f32::MAX as i128 {
          LitFloat::Float(*lhs as f32)
        } else {
          LitFloat::Double(*lhs as f64)
        };
        self.lhs = Expr::Literal(Lit::Float(f));
      },
      (Expr::Literal(Lit::Float(_)), Expr::Literal(Lit::Int(LitInt { value: rhs, suffix: None }))) => {
        let f = if *rhs >= f32::MIN as i128 && *rhs <= f32::MAX as i128 {
          LitFloat::Float(*rhs as f32)
        } else {
          LitFloat::Double(*rhs as f64)
        };
        self.rhs = Expr::Literal(Lit::Float(f));
      },
      (lhs, rhs @ Expr::Literal(Lit::Int(_))) => {
        if let Some(lhs_ty) = max_ty_cast(lhs) {
          self.lhs = Expr::Cast { ty: lhs_ty, expr: Box::new(lhs.clone()) };
        }
      },
      (lhs @ Expr::Literal(Lit::Int(_)), rhs) => {
        if let Some(rhs_ty) = max_ty_cast(rhs) {
          self.rhs = Expr::Cast { ty: rhs_ty, expr: Box::new(rhs.clone()) };
        }
      },
      _ => (),
    }

    Ok((self.lhs.finish(ctx)?, self.rhs.finish(ctx)?))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let lhs = self.lhs.to_token_stream(ctx);
    let op = self.op;
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(match self.op {
      BinaryOp::Assign
      | BinaryOp::AddAssign
      | BinaryOp::SubAssign
      | BinaryOp::BitAndAssign
      | BinaryOp::BitXorAssign
      | BinaryOp::BitOrAssign => {
        quote! { { #lhs #op #rhs; #lhs } }
      },
      op => quote! { ( #lhs #op #rhs ) },
    })
  }
}
