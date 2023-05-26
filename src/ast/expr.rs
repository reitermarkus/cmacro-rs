use std::fmt::Debug;

use nom::{
  branch::alt,
  combinator::{map, map_res, value},
  multi::{fold_many0, separated_list0},
  sequence::{delimited, pair, preceded, terminated, tuple},
  IResult,
};
use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{tokens::parenthesized, *};
use crate::{CodegenContext, LocalContext, MacroArgType, ParseContext, UnaryOp};

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Expr {
  Arg { name: LitIdent },
  Variable { name: Identifier },
  FunctionCall(FunctionCall),
  Cast { expr: Box<Self>, ty: Type },
  Literal(Lit),
  FieldAccess { expr: Box<Self>, field: Box<Self> },
  ArrayAccess { expr: Box<Self>, index: Box<Self> },
  Stringify(Stringify),
  ConcatIdent(Vec<Self>),
  ConcatString(Vec<Self>),
  Unary(Box<UnaryExpr>),
  Binary(Box<BinaryExpr>),
  Ternary(Box<Self>, Box<Self>, Box<Self>),
  Asm(Asm),
}

impl Expr {
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    match self {
      Self::Asm(_) | Self::Literal(_) | Self::Arg { .. } | Self::Variable { .. } | Self::ConcatIdent(_) => (0, None),
      Self::FunctionCall(_) | Self::FieldAccess { .. } => (1, Some(true)),
      Self::Cast { .. } | Self::Stringify(_) | Self::ConcatString(_) => (3, Some(true)),
      Self::Ternary(..) => (0, None),
      // While C array syntax is left associative, Rust precedence is the same as a dereference.
      Self::ArrayAccess { .. } => UnaryOp::Deref.precedence(),
      Self::Unary(expr) => expr.op.precedence(),
      Self::Binary(expr) => expr.op.precedence(),
    }
  }

  /// Parse identifier concatenation, e.g. `arg ## 2`.
  pub(crate) fn parse_concat_ident<'i, 't>(
    tokens: &'i [&'t str],
    ctx: &ParseContext<'_>,
  ) -> IResult<&'i [&'t str], Self> {
    let (tokens, id) = LitIdent::parse(tokens, ctx)?;

    let id = if id.macro_arg { Self::Arg { name: id } } else { Self::Variable { name: Identifier::Literal(id) } };

    fold_many0(
      preceded(delimited(meta::<&'t str>, token::<&'t str>("##"), meta::<&'t str>), |tokens| {
        let (tokens, id) = LitIdent::parse_concat(tokens, ctx)?;
        let id = if id.macro_arg { Self::Arg { name: id } } else { Self::Variable { name: Identifier::Literal(id) } };
        Ok((tokens, id))
      }),
      move || id.clone(),
      |acc, item| match acc {
        Self::ConcatIdent(mut ids) => {
          ids.push(item);
          Self::ConcatIdent(ids)
        },
        expr => Self::ConcatIdent(vec![expr, item]),
      },
    )(tokens)
  }

  /// Parse string concatenation, e.g. `arg "333"`.
  fn parse_concat_string<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let parse_var = |tokens| Self::parse_concat_ident(tokens, ctx);
    let parse_string = alt((
      map(LitString::parse, |s| Self::Literal(Lit::String(s))),
      map(|tokens| Stringify::parse(tokens, ctx), Self::Stringify),
    ));
    let mut parse_part = alt((parse_string, parse_var));

    let (tokens, s) = parse_part(tokens)?;

    fold_many0(
      preceded(meta, parse_part),
      move || s.clone(),
      |mut acc, expr| match acc {
        Self::ConcatString(ref mut args) => {
          args.push(expr);
          acc
        },
        acc => Self::ConcatString(vec![acc, expr]),
      },
    )(tokens)
  }

  fn parse_factor<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    alt((
      map(LitChar::parse, |c| Self::Literal(Lit::Char(c))),
      |tokens| Self::parse_concat_string(tokens, ctx),
      map(Lit::parse, Self::Literal),
      parenthesized(|tokens| Self::parse(tokens, ctx)),
    ))(tokens)
  }

  fn parse_term_prec1<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, factor) = Self::parse_factor(tokens, ctx)?;

    // `__asm ( ... )` or `__asm volatile ( ... )`
    fn is_asm(expr: &Expr) -> bool {
      match expr {
        Expr::Variable { name: Identifier::Literal(ref id) } => matches!(id.as_str(), "__asm__" | "__asm" | "asm"),
        Expr::ConcatString(exprs) => match exprs.as_slice() {
          [first, second] => {
            is_asm(first)
              && matches!(
                second,
                Expr::Variable { name: Identifier::Literal(ref id) }
                if matches!(id.as_str(), "volatile" | "inline" | "goto")
              )
          },
          _ => false,
        },
        _ => false,
      }
    }

    match factor {
      ref expr if is_asm(expr) => {
        if let Ok((tokens, asm)) = Asm::parse(tokens, ctx) {
          return Ok((tokens, Self::Asm(asm)))
        }
      },
      Self::Arg { .. }
      | Self::Variable { .. }
      | Self::FunctionCall(..)
      | Self::FieldAccess { .. }
      | Self::ArrayAccess { .. } => (),
      Self::Unary(ref op) if matches!(&**op, UnaryExpr { op: UnaryOp::AddrOf, .. }) => (),
      _ => return Ok((tokens, factor)),
    }

    enum Access {
      Fn(Vec<Expr>),
      Field { field: Box<Expr>, deref: bool },
      Array { index: Box<Expr> },
      UnaryOp(UnaryOp),
    }

    map_res(
      fold_many0(
        preceded(
          meta,
          alt((
            map(
              parenthesized(separated_list0(tuple((meta, token(","), meta)), |tokens| Self::parse(tokens, ctx))),
              Access::Fn,
            ),
            map(preceded(terminated(token("."), meta), |tokens| Self::parse_concat_ident(tokens, ctx)), |field| {
              Access::Field { field: Box::new(field), deref: false }
            }),
            map(
              delimited(terminated(token("["), meta), |tokens| Self::parse(tokens, ctx), preceded(meta, token("]"))),
              |index| Access::Array { index: Box::new(index) },
            ),
            map(preceded(terminated(token("->"), meta), |tokens| Self::parse_concat_ident(tokens, ctx)), |field| {
              Access::Field { field: Box::new(field), deref: true }
            }),
            map(alt((value(UnaryOp::PostInc, token("++")), value(UnaryOp::PostDec, token("--")))), |op| {
              Access::UnaryOp(op)
            }),
          )),
        ),
        move || Ok((factor.clone(), false)),
        |acc, access| {
          let (expr, was_unary_op) = acc?;
          let is_unary_op = matches!(access, Access::UnaryOp(_));

          Ok((
            match (expr, access) {
              // Postfix `++`/`--` cannot be chained.
              (expr, Access::UnaryOp(op)) if !was_unary_op => Self::Unary(Box::new(UnaryExpr { expr, op })),
              // TODO: Support calling expressions as functions.
              (name @ Self::Arg { .. } | name @ Self::Variable { .. }, Access::Fn(args)) => {
                Self::FunctionCall(FunctionCall { name: Box::new(name), args })
              },
              // Field access cannot be chained after postfix `++`/`--`.
              (acc, Access::Field { field, deref }) if !was_unary_op || deref => {
                let acc = if deref { Self::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: acc })) } else { acc };
                Self::FieldAccess { expr: Box::new(acc), field }
              },
              // Array access cannot be chained after postfix `++`/`--`.
              (acc, Access::Array { index }) if !was_unary_op => Self::ArrayAccess { expr: Box::new(acc), index },
              _ => return Err(()),
            },
            is_unary_op,
          ))
        },
      ),
      |res| res.map(|(expr, _)| expr),
    )(tokens)
  }

  fn parse_term_prec2<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    alt((
      map(
        pair(parenthesized(|tokens| Type::parse(tokens, ctx)), |tokens| Self::parse_term_prec2(tokens, ctx)),
        |(ty, term)| Self::Cast { expr: Box::new(term), ty },
      ),
      map(
        pair(
          terminated(
            alt((
              value(UnaryOp::Deref, token("*")),
              value(UnaryOp::AddrOf, token("&")),
              value(UnaryOp::Inc, token("++")),
              value(UnaryOp::Dec, token("--")),
              value(UnaryOp::Plus, token("+")),
              value(UnaryOp::Minus, token("-")),
              value(UnaryOp::Not, token("!")),
              value(UnaryOp::Comp, token("~")),
            )),
            meta,
          ),
          |tokens| Self::parse_term_prec2(tokens, ctx),
        ),
        |(op, expr)| Self::Unary(Box::new(UnaryExpr { op, expr })),
      ),
      |tokens| Self::parse_term_prec1(tokens, ctx),
    ))(tokens)
  }

  fn parse_term_prec3<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec2(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((value(BinaryOp::Mul, token("*")), value(BinaryOp::Div, token("/")), value(BinaryOp::Rem, token("%")))),
          meta,
        ),
        |tokens| Self::parse_term_prec2(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec4<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec3(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Add, token("+")), value(BinaryOp::Sub, token("-")))), meta),
        |tokens| Self::parse_term_prec3(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec5<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec4(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Shl, token("<<")), value(BinaryOp::Shr, token(">>")))), meta),
        |tokens| Self::parse_term_prec4(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec6<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec5(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((
            value(BinaryOp::Lt, token("<")),
            value(BinaryOp::Lte, token("<=")),
            value(BinaryOp::Gt, token(">")),
            value(BinaryOp::Gte, token(">=")),
          )),
          meta,
        ),
        |tokens| Self::parse_term_prec5(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec7<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec6(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Eq, token("==")), value(BinaryOp::Neq, token("!=")))), meta),
        |tokens| Self::parse_term_prec6(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec8<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec7(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("&"), meta), |tokens| Self::parse_term_prec7(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitAnd, rhs })),
    )(tokens)
  }

  fn parse_term_prec9<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec8(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("^"), meta), |tokens| Self::parse_term_prec8(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitXor, rhs })),
    )(tokens)
  }

  fn parse_term_prec10<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec9(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("|"), meta), |tokens| Self::parse_term_prec9(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitOr, rhs })),
    )(tokens)
  }

  fn parse_term_prec13<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec10(tokens, ctx)?;

    // Parse ternary.
    if let Ok((tokens, _)) = delimited(meta, token("?"), meta)(tokens) {
      let (tokens, if_branch) = Self::parse_term_prec7(tokens, ctx)?;
      let (tokens, _) = delimited(meta, token(":"), meta)(tokens)?;
      let (tokens, else_branch) = Self::parse_term_prec7(tokens, ctx)?;
      return Ok((tokens, Self::Ternary(Box::new(term), Box::new(if_branch), Box::new(else_branch))))
    }

    Ok((tokens, term))
  }

  fn parse_term_prec14<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec13(tokens, ctx)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((
            value(BinaryOp::Assign, token("=")),
            value(BinaryOp::AddAssign, token("+=")),
            value(BinaryOp::SubAssign, token("-=")),
            value(BinaryOp::MulAssign, token("*=")),
            value(BinaryOp::DivAssign, token("/=")),
            value(BinaryOp::RemAssign, token("%=")),
            value(BinaryOp::ShlAssign, token("<<=")),
            value(BinaryOp::ShrAssign, token(">>=")),
            value(BinaryOp::BitAndAssign, token("&=")),
            value(BinaryOp::BitXorAssign, token("^=")),
            value(BinaryOp::BitOrAssign, token("|=")),
          )),
          meta,
        ),
        |tokens| Self::parse_term_prec14(tokens, ctx),
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  /// Parse an expression.
  pub(crate) fn parse<'i, 't>(tokens: &'i [&'t str], ctx: &ParseContext<'_>) -> IResult<&'i [&'t str], Self> {
    Self::parse_term_prec14(tokens, ctx)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::Cast { expr, ty } => {
        expr.finish(ctx)?;

        // Handle ambiguous cast vs. binary operation, e.g. `(ty)&var` vs `(var1) & var2`.
        if let (Self::Unary(expr), Type::Identifier { name, is_struct: false }) = (&**expr, &ty) {
          let treat_as_binop = match **name {
            Self::Arg { .. } => {
              // Arguments cannot be resolved as a type.
              true
            },
            Self::Variable { name: Identifier::Literal(ref id) } => {
              // Cannot resolve type.
              ctx.resolve_ty(id.as_str()).is_none()
            },
            _ => true,
          };

          if treat_as_binop {
            let op = match expr.op {
              UnaryOp::Plus => Some(BinaryOp::Add),
              UnaryOp::Minus => Some(BinaryOp::Sub),
              UnaryOp::Deref => Some(BinaryOp::Mul),
              UnaryOp::AddrOf => Some(BinaryOp::BitAnd),
              _ => None,
            };

            if let Some(op) = op {
              let lhs = (**name).clone();
              let rhs = expr.expr.clone();

              *self = Self::Binary(Box::new(BinaryExpr { lhs, op, rhs }));
              return self.finish(ctx)
            }
          }
        }

        // Remove redundant casts from string literals, e.g. `(char*)"adsf"`.
        if matches!(
          (&**expr, &ty), (Expr::Literal(Lit::String(LitString::Ordinary(_))), Type::Ptr { ty, .. })
          if matches!(**ty, Type::BuiltIn(BuiltInType::Char))
        ) {
          *self = (**expr).clone();
          return self.finish(ctx)
        }

        ty.finish(ctx)?;
        Ok(Some(ty.clone()))
      },
      Self::Arg { ref mut name } => {
        if let Some(arg_ty) = ctx.arg_type_mut(name.as_str()) {
          if let MacroArgType::Known(arg_ty) = arg_ty {
            return Ok(Some(arg_ty.clone()))
          }
        }

        Ok(None)
      },
      Self::Variable { ref mut name } => {
        name.finish(ctx)?;

        match name {
          Identifier::Literal(name) => {
            // Built-in macros.
            return match name.as_str() {
              "__SCHAR_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::SChar))),
              "__SHRT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Short))),
              "__INT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Int))),
              "__LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Long))),
              "__LONG_LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::LongLong))),
              _ => Ok(None),
            }
          },
          Identifier::Concat(_) => Ok(None),
        }
      },
      Self::FunctionCall(call) => {
        let ty = call.finish(ctx)?;

        match *call.name {
          Self::Variable { name: Identifier::Literal(ref id) } if ctx.function(id.as_str()).is_some() => Ok(ty),
          _ => {
            // Type should only be set if calling an actual function, not a function macro.
            Ok(ty)
          },
        }
      },
      // Convert character literals to casts.
      Self::Literal(lit) if matches!(lit, Lit::Char(..)) => {
        let ty = lit.finish(ctx)?;
        *self = Self::Cast { expr: Box::new(Self::Literal(lit.clone())), ty: ty.clone().unwrap() };
        Ok(ty)
      },
      Self::Literal(lit) => lit.finish(ctx),
      Self::FieldAccess { expr, field } => {
        expr.finish(ctx)?;
        field.finish(ctx)?;

        if let Self::Arg { ref name } = **field {
          if let Some(arg_type) = ctx.arg_type_mut(name.as_str()) {
            *arg_type = MacroArgType::Ident;
          }
        }

        Ok(None)
      },
      Self::ArrayAccess { expr, index } => {
        let expr_ty = expr.finish(ctx)?;
        index.finish(ctx)?;

        match expr_ty {
          Some(Type::Ptr { ty, .. }) => Ok(Some(*ty)),
          None => Ok(None),
          // Type can only be either a pointer-type or unknown.
          _ => Err(crate::CodegenError::UnsupportedExpression),
        }
      },
      Self::Stringify(stringify) => stringify.finish(ctx),
      Self::ConcatIdent(ref mut ids) => {
        let mut new_ids = vec![];

        for id in ids.drain(..) {
          match id {
            Self::Arg { name } => {
              if let Some(arg_type) = ctx.arg_type_mut(name.as_str()) {
                *arg_type = MacroArgType::Ident;
              }

              new_ids.push(Self::Arg { name });
            },
            Self::Variable { name: Identifier::Literal(id) } => {
              if let Some(Self::Variable { name: Identifier::Literal(last_id) }) = new_ids.last_mut() {
                last_id.id.push_str(&id.id)
              } else {
                new_ids.push(Self::Variable { name: Identifier::Literal(id) });
              }
            },
            _ => {
              // This should be unreachable, since only `Arg` and `Variable` are ever added to `ConcatIdent`.
              return Err(crate::CodegenError::UnsupportedExpression)
            },
          }
        }

        if new_ids.len() == 1 {
          *self = new_ids.remove(0);
          self.finish(ctx)
        } else {
          *ids = new_ids;

          for id in ids.iter_mut() {
            id.finish(ctx)?;
          }

          Ok(None)
        }
      },
      Self::ConcatString(names) => {
        let mut new_names = vec![];
        let mut current_name: Option<Vec<u8>> = None;

        for name in &mut *names {
          name.finish(ctx)?;

          if let Self::Literal(Lit::String(lit)) = name {
            if let Some(lit_bytes) = lit.as_bytes() {
              if let Some(ref mut current_name) = current_name {
                current_name.extend_from_slice(lit_bytes);
              } else {
                current_name = Some(lit_bytes.to_vec());
              }
              continue
            } else {
              // FIXME: Cannot concatenate wide strings due to unknown size of `wchar_t`.
              return Err(crate::CodegenError::UnsupportedExpression)
            }
          }

          if let Some(current_name) = current_name.take() {
            new_names.push(Self::Literal(Lit::String(LitString::Ordinary(current_name))));
          }

          new_names.push(name.clone());
        }

        if let Some(current_name) = current_name.take() {
          new_names.push(Self::Literal(Lit::String(LitString::Ordinary(current_name))));
        }

        if new_names.len() == 1 {
          *self = new_names.remove(0);
          self.finish(ctx)
        } else {
          *self = Self::ConcatString(new_names);
          Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
        }
      },
      Self::Unary(op) => {
        let ty = op.finish(ctx)?;

        match (op.op, &op.expr) {
          (UnaryOp::Plus, expr @ Self::Literal(Lit::Int(_)) | expr @ Self::Literal(Lit::Float(_))) => {
            *self = expr.clone();
          },
          (UnaryOp::Minus, Self::Literal(Lit::Int(LitInt { value: i, suffix }))) => {
            let suffix = match suffix {
              Some(BuiltInType::UChar | BuiltInType::SChar) => Some(BuiltInType::SChar),
              Some(BuiltInType::UInt | BuiltInType::Int) => Some(BuiltInType::Int),
              Some(BuiltInType::ULong | BuiltInType::Long) => Some(BuiltInType::Long),
              Some(BuiltInType::ULongLong | BuiltInType::LongLong) => Some(BuiltInType::LongLong),
              _ => None,
            };
            *self = Self::Literal(Lit::Int(LitInt { value: i.wrapping_neg(), suffix }));
          },
          (UnaryOp::Minus, Self::Literal(Lit::Float(f))) => {
            *self = Self::Literal(Lit::Float(match f {
              LitFloat::Float(f) => LitFloat::Float(-f),
              LitFloat::Double(f) => LitFloat::Double(-f),
              LitFloat::LongDouble(f) => LitFloat::LongDouble(-f),
            }));
          },
          (UnaryOp::Not, Self::Literal(Lit::Int(LitInt { value: i, suffix: None }))) => {
            *self = Self::Literal(Lit::Int(LitInt { value: (*i == 0).into(), suffix: None }));
          },
          (UnaryOp::Not, Self::Literal(Lit::Float(f))) => {
            *self = Self::Literal(Lit::Int(LitInt {
              value: match f {
                LitFloat::Float(f) => *f == 0.0,
                LitFloat::Double(f) => *f == 0.0,
                LitFloat::LongDouble(f) => *f == 0.0,
              } as i128,
              suffix: None,
            }));
          },
          (UnaryOp::Not, expr) => {
            if ty != Some(Type::BuiltIn(BuiltInType::Bool)) {
              let lhs = expr.clone();
              let rhs = match ty {
                Some(Type::BuiltIn(BuiltInType::Float)) => Self::Literal(Lit::Float(LitFloat::Float(0.0))),
                Some(Type::BuiltIn(BuiltInType::Double)) => Self::Literal(Lit::Float(LitFloat::Double(0.0))),
                Some(Type::BuiltIn(BuiltInType::LongDouble)) => Self::Literal(Lit::Float(LitFloat::LongDouble(0.0))),
                _ => Self::Literal(Lit::Int(LitInt { value: 0, suffix: None })),
              };

              *self = Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::Eq, rhs }))
            }
          },
          (UnaryOp::Comp, Self::Literal(Lit::Float(_) | Lit::String(_))) => {
            return Err(crate::CodegenError::UnsupportedExpression)
          },
          _ => (),
        }

        Ok(ty)
      },
      Self::Binary(op) => {
        let (lhs_ty, rhs_ty) = op.finish(ctx)?;

        // Calculate numeric expression.
        match (op.op, &op.lhs, &op.rhs) {
          (BinaryOp::Mul, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs * *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Mul, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs * *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Div, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs / *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Div, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs / *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Rem, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs % *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Add, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs + *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Add, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs + *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Sub, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs - *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Sub, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs - *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Shl, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs << *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Shr, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs >> *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitAnd, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs & *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitOr, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs | *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitXor, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs ^ *rhs));
            self.finish(ctx)
          },
          (
            BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::And
            | BinaryOp::Or
            | BinaryOp::Lt
            | BinaryOp::Lte
            | BinaryOp::Gt
            | BinaryOp::Gte,
            _,
            _,
          ) => Ok(Some(Type::BuiltIn(BuiltInType::Bool))),
          _ => {
            if lhs_ty == rhs_ty {
              Ok(lhs_ty)
            } else {
              Ok(lhs_ty.xor(rhs_ty))
            }
          },
        }
      },
      Self::Ternary(cond, if_branch, else_branch) => {
        cond.finish(ctx)?;
        let lhs_ty = if_branch.finish(ctx)?;
        let rhs_ty = else_branch.finish(ctx)?;

        if lhs_ty == rhs_ty {
          Ok(lhs_ty)
        } else {
          Ok(lhs_ty.xor(rhs_ty))
        }
      },
      Self::Asm(asm) => asm.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    match self {
      Self::Cast { ref expr, ref ty } => tokens.append_all(match (ty, &**expr) {
        (Type::Ptr { mutable, .. }, Expr::Literal(Lit::Int(LitInt { value: 0, .. }))) => {
          let prefix = ctx.trait_prefix().into_iter();

          if *mutable {
            quote! { #(#prefix::)*ptr::null_mut() }
          } else {
            quote! { #(#prefix::)*ptr::null() }
          }
        },
        (ty, expr) => {
          if ty.is_void() {
            let expr = expr.to_token_stream(ctx);
            quote! { { drop(#expr) } }
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
      }),
      Self::Arg { ref name } => tokens.append_all(match name.as_str() {
        "__VA_ARGS__" => quote! { $($__VA_ARGS__),* },
        name => {
          let name = Ident::new(name, Span::call_site());

          if ctx.export_as_macro {
            quote! { $#name }
          } else {
            quote! { #name }
          }
        },
      }),
      Self::Variable { ref name } => {
        if let Identifier::Literal(name) = name {
          let prefix = ctx.ffi_prefix().into_iter();

          match name.as_str() {
            "__SCHAR_MAX__" => return tokens.append_all(quote! { #(#prefix::)*c_schar::MAX }),
            "__SHRT_MAX__" => return tokens.append_all(quote! { #(#prefix::)*c_short::MAX }),
            "__INT_MAX__" => return tokens.append_all(quote! { #(#prefix::)*c_int::MAX }),
            "__LONG_MAX__" => return tokens.append_all(quote! { #(#prefix::)*c_long::MAX }),
            "__LONG_LONG_MAX__" => return tokens.append_all(quote! { #(#prefix::)*c_longlong::MAX }),
            _ => (),
          }
        }

        name.to_tokens(ctx, tokens)
      },
      Self::FunctionCall(ref call) => {
        call.to_tokens(ctx, tokens);
      },
      Self::Literal(ref lit) => lit.to_tokens(ctx, tokens),
      Self::FieldAccess { ref expr, ref field } => {
        let (prec, _) = self.precedence();
        let (expr_prec, _) = expr.precedence();

        let mut expr = expr.to_token_stream(ctx);
        if expr_prec > prec {
          expr = quote! { (#expr) };
        }

        let field = field.to_token_stream(ctx);

        tokens.append_all(format!("{}.{}", expr, field).parse::<TokenStream>().unwrap())
      },
      Self::ArrayAccess { ref expr, ref index } => {
        let (expr_prec, _) = expr.precedence();

        let mut expr = expr.to_token_stream(ctx);
        // `self.precedence()` does not work here since array access is represented
        // as a method call followed by a dereference.
        if expr_prec > 1 {
          expr = quote! { (#expr) };
        }

        let index = index.to_token_stream(ctx);
        tokens.append_all(quote! { *#expr.offset(#index) })
      },
      Self::Stringify(stringify) => {
        stringify.to_tokens(ctx, tokens);
      },
      Self::ConcatIdent(ids) => {
        let trait_prefix = ctx.trait_prefix().into_iter();
        let ids = ids.iter().map(|id| id.to_token_stream(ctx));
        tokens.append_all(quote! { #(#trait_prefix::)*concat_idents!(#(#ids),*) })
      },
      Self::ConcatString(ref names) => {
        let ffi_prefix = ctx.ffi_prefix().into_iter();
        let trait_prefix = ctx.trait_prefix().into_iter();

        let names = names
          .iter()
          .map(|e| match e {
            Self::Stringify(s) => {
              let id = s.id.to_token_stream(ctx);
              let trait_prefix = trait_prefix.clone();

              quote! { #(#trait_prefix::)*stringify!(#id) }
            },
            e => e.to_token_stream(ctx),
          })
          .collect::<Vec<_>>();

        tokens.append_all(quote! {
          {
            const BYTES: &[u8] = #(#trait_prefix::)*concat!(#(#names),*, '\0').as_bytes();
            BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
          }
        })
      },
      Self::Unary(op) => op.to_tokens(ctx, tokens),
      Self::Binary(op) => op.to_tokens(ctx, tokens),
      Self::Ternary(ref cond, ref if_branch, ref else_branch) => {
        let cond = cond.to_token_stream(ctx);
        let if_branch = if_branch.to_token_stream(ctx);
        let else_branch = else_branch.to_token_stream(ctx);

        tokens.append_all(quote! {
          if #cond {
            #if_branch
          } else {
            #else_branch
          }
        })
      },
      Self::Asm(ref asm) => asm.to_tokens(ctx, tokens),
    }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const CTX: ParseContext = ParseContext::var_macro("EXPR");

  #[test]
  fn parse_literal() {
    let (_, expr) = Expr::parse(&["u8", "'a'"], &CTX).unwrap();
    assert_eq!(expr, lit!(u8 'a'));

    let (_, expr) = Expr::parse(&["U'🍩'"], &CTX).unwrap();
    assert_eq!(expr, lit!(U '🍩'));
  }

  #[test]
  fn parse_stringify() {
    let ctx = ParseContext::fn_macro("EXPR", &["a"]);
    let (_, expr) = Expr::parse(&["#", "$a"], &ctx).unwrap();
    assert_eq!(expr, Expr::Stringify(Stringify { id: id!(@a) }));
  }

  #[test]
  fn parse_concat() {
    let (_, expr) = Expr::parse(&[r#""abc""#, r#""def""#], &CTX).unwrap();
    assert_eq!(expr, Expr::Literal(Lit::String(LitString::Ordinary("abcdef".into()))));

    let ctx = ParseContext::fn_macro("EXPR", &["a"]);
    let (_, expr) = Expr::parse(&[r#""def""#, "#", "$a"], &ctx).unwrap();
    assert_eq!(
      expr,
      Expr::ConcatString(vec![
        Expr::Literal(Lit::String(LitString::Ordinary("def".into()))),
        Expr::Stringify(Stringify { id: id!(@a) }),
      ])
    );
  }

  #[test]
  fn parse_concat_ident() {
    let ctx = ParseContext::fn_macro("IDENTIFIER", &["abc"]);

    let (_, id) = Expr::parse(&["$abc", "##", "def"], &ctx).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(abc), var!(def)]));

    let (_, id) = Expr::parse(&["$abc", "##", "def", "##", "ghi"], &ctx).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(abc), var!(def), var!(ghi)]));

    let (_, id) = Expr::parse(&["$abc", "##", "_def"], &ctx).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(abc), var!(_def)]));

    let (_, id) = Expr::parse(&["$abc", "##", "123"], &ctx).unwrap();
    assert_eq!(
      id,
      Expr::ConcatIdent(vec![
        arg!(abc),
        Expr::Variable { name: Identifier::Literal(LitIdent { id: "123".into(), macro_arg: false }) }
      ])
    );

    let (_, id) = Expr::parse(&["__INT", "##", "_MAX__"], &CTX).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![var!(__INT), var!(_MAX__)]));
  }

  #[test]
  fn parse_field_access() {
    let (_, expr) = Expr::parse(&["a", ".", "b"], &CTX).unwrap();
    assert_eq!(expr, Expr::FieldAccess { expr: Box::new(var!(a)), field: Box::new(var!(b)) });
  }

  #[test]
  fn parse_pointer_access() {
    let (_, expr) = Expr::parse(&["a", "->", "b"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::FieldAccess {
        expr: Box::new(Expr::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: var!(a) }))),
        field: Box::new(var!(b))
      }
    );
  }

  #[test]
  fn parse_array_access() {
    let (_, expr) = Expr::parse(&["a", "[", "0", "]"], &CTX).unwrap();
    assert_eq!(expr, Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(lit!(0)) });

    let (_, expr) = Expr::parse(&["a", "[", "0", "]", "[", "1", "]"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::ArrayAccess {
        expr: Box::new(Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(lit!(0)) }),
        index: Box::new(lit!(1))
      }
    );

    let (_, expr) = Expr::parse(&["a", "[", "b", "]"], &CTX).unwrap();
    assert_eq!(expr, Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(var!(b)) });
  }

  #[test]
  fn parse_assignment() {
    let (_, expr) = Expr::parse(&["a", "=", "b", "=", "c"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::Binary(Box::new(BinaryExpr {
        lhs: var!(a),
        op: BinaryOp::Assign,
        rhs: Expr::Binary(Box::new(BinaryExpr { lhs: var!(b), op: BinaryOp::Assign, rhs: var!(c) }),),
      }))
    );
  }

  #[test]
  fn parse_function_call() {
    let (_, expr) = Expr::parse(&["my_function", "(", "arg1", ",", "arg2", ")"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::FunctionCall(FunctionCall {
        name: Box::new(Expr::Variable {
          name: Identifier::Literal(LitIdent { id: "my_function".into(), macro_arg: false })
        }),
        args: vec![var!(arg1), var!(arg2)]
      })
    );
  }

  #[test]
  fn parse_paren() {
    let (_, expr) = Expr::parse(&["(", "-", "123456789012ULL", ")"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::Unary(Box::new(UnaryExpr {
        op: UnaryOp::Minus,
        expr: Expr::Literal(Lit::Int(LitInt { value: 123456789012, suffix: Some(BuiltInType::ULongLong) }))
      }))
    )
  }
}
