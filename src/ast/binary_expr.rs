use std::fmt::Debug;

use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use crate::{CodegenContext, Expr, LocalContext, MacroArgType};

use super::{BuiltInType, Cast, Lit, LitFloat, LitInt, Type, Var};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Associativity {
  None,
  Left,
  Right,
}

/// A binary expression operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
  /// `lhs * rhs`
  Mul,
  /// `lhs / rhs`
  Div,
  /// `lhs % rhs`
  Rem,
  /// `lhs + rhs`
  Add,
  /// `lhs - rhs`
  Sub,
  /// `lhs << rhs`
  Shl,
  /// `lhs >> rhs`
  Shr,
  /// `lhs < rhs`
  Lt,
  /// `lhs <= rhs`
  Lte,
  /// `lhs > rhs`
  Gt,
  /// `lhs >= rhs`
  Gte,
  /// `lhs == rhs`
  Eq,
  /// `lhs != rhs`
  Neq,
  /// `lhs & rhs`
  BitAnd,
  /// `lhs ^ rhs`
  BitXor,
  /// `lhs | rhs`
  BitOr,
  /// `lhs && rhs`
  And,
  /// `lhs || rhs`
  Or,
  /// `lhs = rhs`
  Assign,
  /// `lhs += rhs`
  AddAssign,
  /// `lhs -= rhs`
  SubAssign,
  /// `lhs *= rhs`
  MulAssign,
  /// `lhs /= rhs`
  DivAssign,
  /// `lhs %= rhs`
  RemAssign,
  /// `lhs <<= rhs`
  ShlAssign,
  /// `lhs >>= rhs`
  ShrAssign,
  /// `lhs &= rhs`
  BitAndAssign,
  /// `lhs ^= rhs`
  BitXorAssign,
  /// `lhs |= rhs`
  BitOrAssign,
  /// `lhs.rhs`
  MemberAccess,
}

impl BinaryOp {
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    match self {
      Self::MemberAccess => (1, Associativity::Left),
      Self::Mul | Self::Div | Self::Rem => (5, Associativity::Left),
      Self::Add | Self::Sub => (6, Associativity::Left),
      Self::Shl | Self::Shr => (7, Associativity::Left),

      Self::BitAnd => (8, Associativity::Left),
      Self::BitXor => (9, Associativity::Left),
      Self::BitOr => (10, Associativity::Left),

      Self::Eq | Self::Neq | Self::Lt | Self::Gt | Self::Lte | Self::Gte => (11, Associativity::None),

      Self::And => (12, Associativity::Left),
      Self::Or => (13, Associativity::Left),
      Self::Assign
      | Self::AddAssign
      | Self::SubAssign
      | Self::MulAssign
      | Self::DivAssign
      | Self::RemAssign
      | Self::ShlAssign
      | Self::ShrAssign
      | Self::BitAndAssign
      | Self::BitXorAssign
      | Self::BitOrAssign => (14, Associativity::Right),
    }
  }
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
      Self::MemberAccess => quote! { . },
    })
  }
}

/// A binary expression.
///
/// ```c
/// #define BINARY_EXPR a + b
/// #define BINARY_EXPR 1 + 2
/// #define BINARY_EXPR 7 % c
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryExpr<'t> {
  /// Left-hand side expression.
  pub lhs: Box<Expr<'t>>,
  /// Expression operator.
  pub op: BinaryOp,
  /// Right-hand side expression.
  pub rhs: Box<Expr<'t>>,
}

impl<'t> BinaryExpr<'t> {
  #[inline]
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    self.op.precedence()
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    let max_ty_cast = |expr: &Expr| {
      if let Expr::Var(Var { name }) = expr {
        return Some(Type::BuiltIn(match name.as_str() {
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

    let mut lhs_ty = self.lhs.finish(ctx)?;
    let mut rhs_ty = self.rhs.finish(ctx)?;

    // Cast mixed float and int expression.
    match (&*self.lhs, &*self.rhs) {
      (_, Expr::Arg(arg)) if self.op == BinaryOp::MemberAccess => {
        // Arg must be an identifier for use as a member name.
        *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
      },
      (Expr::Literal(Lit::Int(LitInt { value: lhs, suffix: None })), Expr::Literal(Lit::Float(_))) => {
        let f = if *lhs >= f32::MIN as i128 && *lhs <= f32::MAX as i128 {
          LitFloat::Float(*lhs as f32)
        } else {
          LitFloat::Double(*lhs as f64)
        };
        self.lhs = Box::new(Expr::Literal(Lit::Float(f)));
        lhs_ty = self.lhs.finish(ctx)?;
      },
      (Expr::Literal(Lit::Float(_)), Expr::Literal(Lit::Int(LitInt { value: rhs, suffix: None }))) => {
        let f = if *rhs >= f32::MIN as i128 && *rhs <= f32::MAX as i128 {
          LitFloat::Float(*rhs as f32)
        } else {
          LitFloat::Double(*rhs as f64)
        };
        self.rhs = Box::new(Expr::Literal(Lit::Float(f)));
        rhs_ty = self.rhs.finish(ctx)?;
      },
      (lhs, Expr::Literal(Lit::Int(_))) => {
        if let Some(lhs_ty2) = max_ty_cast(lhs) {
          self.lhs = Box::new(Expr::Cast(Cast { ty: lhs_ty2.clone(), expr: Box::new(lhs.clone()) }));
          lhs_ty = Some(lhs_ty2);
        }
      },
      (Expr::Literal(Lit::Int(_)), rhs) => {
        if let Some(rhs_ty2) = max_ty_cast(rhs) {
          self.rhs = Box::new(Expr::Cast(Cast { ty: rhs_ty2.clone(), expr: Box::new(rhs.clone()) }));
          rhs_ty = Some(rhs_ty2);
        }
      },
      _ => (),
    }

    if self.op == BinaryOp::MemberAccess {
      // TODO: Get type of struct field.
      return Ok(None)
    }

    // Type can only be inferred if both sides have the same type.
    if lhs_ty == rhs_ty {
      return Ok(lhs_ty)
    }

    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut lhs = self.lhs.to_token_stream(ctx);
    let op = self.op;
    let mut rhs = self.rhs.to_token_stream(ctx);

    let (lhs_prec, _) = self.lhs.precedence();
    let (prec, assoc) = self.precedence();
    let (rhs_prec, _) = self.rhs.precedence();

    let (lhs_parens, rhs_parens) = match (prec, assoc) {
      (_, Associativity::None) => (lhs_prec >= prec, rhs_prec >= prec),
      (_, Associativity::Left) => (lhs_prec > prec, rhs_prec >= prec),
      (_, Associativity::Right) => (lhs_prec <= prec, rhs_prec < prec),
    };

    match self.op {
      BinaryOp::Assign
      | BinaryOp::AddAssign
      | BinaryOp::SubAssign
      | BinaryOp::BitAndAssign
      | BinaryOp::BitXorAssign
      | BinaryOp::BitOrAssign => {
        quote! { { #lhs #op #rhs; #lhs } }
      },
      op => {
        if lhs_parens {
          lhs = quote! { (#lhs) };
        }
        if rhs_parens {
          rhs = quote! { (#rhs) };
        }

        quote! { #lhs #op #rhs }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::{
    super::{assert_eq_tokens, lit, var},
    *,
  };

  #[test]
  fn parentheses_add_mul() {
    let expr1 = BinaryExpr { lhs: Box::new(lit!(1)), op: BinaryOp::Add, rhs: Box::new(lit!(2)) };
    assert_eq_tokens!(expr1, "1 + 2");

    let expr2 = BinaryExpr { lhs: Box::new(Expr::Binary(expr1.clone())), op: BinaryOp::Add, rhs: Box::new(lit!(3)) };
    assert_eq_tokens!(expr2, "1 + 2 + 3");

    let expr3 = BinaryExpr { lhs: Box::new(Expr::Binary(expr1.clone())), op: BinaryOp::Mul, rhs: Box::new(lit!(3)) };
    assert_eq_tokens!(expr3, "(1 + 2) * 3");
  }

  #[test]
  fn parentheses_neq() {
    let expr1 = BinaryExpr { lhs: Box::new(lit!(1)), op: BinaryOp::Neq, rhs: Box::new(lit!(2)) };
    assert_eq_tokens!(expr1, "1 != 2");
  }

  #[test]
  fn parentheses_eq() {
    let expr1 = BinaryExpr { lhs: Box::new(lit!(1)), op: BinaryOp::BitAnd, rhs: Box::new(lit!(2)) };
    assert_eq_tokens!(expr1, "1 & 2");

    let expr2 = BinaryExpr { lhs: Box::new(Expr::Binary(expr1)), op: BinaryOp::Eq, rhs: Box::new(lit!(3)) };
    assert_eq_tokens!(expr2, "1 & 2 == 3");
  }

  #[test]
  fn parentheses_rem_div() {
    let expr1 = BinaryExpr { lhs: Box::new(lit!(6)), op: BinaryOp::Rem, rhs: Box::new(lit!(9)) };
    assert_eq_tokens!(expr1, "6 % 9");

    let expr2 = BinaryExpr { lhs: Box::new(Expr::Binary(expr1)), op: BinaryOp::Div, rhs: Box::new(lit!(3)) };
    assert_eq_tokens!(expr2, "6 % 9 / 3");

    let expr3 = BinaryExpr { lhs: Box::new(lit!(9)), op: BinaryOp::Div, rhs: Box::new(lit!(3)) };
    assert_eq_tokens!(expr3, "9 / 3");

    let expr4 = BinaryExpr { lhs: Box::new(lit!(6)), op: BinaryOp::Rem, rhs: Box::new(Expr::Binary(expr3)) };
    assert_eq_tokens!(expr4, "6 % (9 / 3)");
  }

  #[test]
  fn parentheses_assign() {
    let expr1 = BinaryExpr { lhs: Box::new(var!(a)), op: BinaryOp::Assign, rhs: Box::new(var!(b)) };
    assert_eq_tokens!(expr1, "{ a = b; a }");

    let expr2 = BinaryExpr { lhs: Box::new(var!(c)), op: BinaryOp::Assign, rhs: Box::new(Expr::Binary(expr1)) };
    assert_eq_tokens!(expr2, "{ c = { a = b; a }; c }");
  }
}
