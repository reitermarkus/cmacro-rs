use std::{
  fmt::Debug,
  ops::{RangeFrom, RangeTo},
};

use nom::{
  branch::alt,
  combinator::{map, map_res, value},
  multi::{fold_many0, separated_list0},
  sequence::{delimited, pair, preceded, terminated, tuple},
  AsChar, Compare, FindSubstring, FindToken, IResult, InputIter, InputLength, InputTake, InputTakeAtPosition, Offset,
  ParseTo, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{tokens::parenthesized, *};
use crate::{CodegenContext, LocalContext, MacroArgType, MacroBody, ParseContext, UnaryOp};

/// An expression.
#[derive(Debug, Clone, PartialEq)]
#[allow(missing_docs)]
pub enum Expr {
  Variable { name: Identifier },
  FunctionCall(FunctionCall),
  Cast { expr: Box<Self>, ty: Type },
  Literal(Lit),
  FieldAccess { expr: Box<Self>, field: Identifier },
  Stringify(Stringify),
  Concat(Vec<Self>),
  Unary(Box<UnaryExpr>),
  Binary(Box<BinaryExpr>),
  Ternary(Box<Self>, Box<Self>, Box<Self>),
  Asm(Asm),
}

impl Expr {
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    match self {
      Self::Asm(_) | Self::Literal(_) | Self::Variable { .. } => (0, None),
      Self::FunctionCall(_) | Self::FieldAccess { .. } => (1, Some(true)),
      Self::Cast { .. } | Self::Stringify(_) | Self::Concat(_) => (3, Some(true)),
      Self::Ternary(..) => (0, None),
      Self::Unary(expr) => expr.op.precedence(),
      Self::Binary(expr) => expr.op.precedence(),
    }
  }

  fn parse_concat<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let parse_var = map(|tokens| Identifier::parse(tokens, ctx), |id| Self::Variable { name: id });
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
        Self::Concat(ref mut args) => {
          args.push(expr);
          acc
        },
        acc => Self::Concat(vec![acc, expr]),
      },
    )(tokens)
  }

  fn parse_factor<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    alt((
      map(LitChar::parse, |c| Self::Literal(Lit::Char(c))),
      |tokens| Self::parse_concat(tokens, ctx),
      map(Lit::parse, Self::Literal),
      parenthesized(|tokens| Self::parse(tokens, ctx)),
    ))(tokens)
  }

  fn parse_term_prec1<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, factor) = Self::parse_factor(tokens, ctx)?;

    // `__asm ( ... )` or `__asm volatile ( ... )`
    fn is_asm(expr: &Expr) -> bool {
      match expr {
        Expr::Variable { name: Identifier::Literal(ref id) } => matches!(id.as_str(), "__asm__" | "__asm" | "asm"),
        Expr::Concat(exprs) => match exprs.as_slice() {
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
      Self::Variable { .. } | Self::FunctionCall(..) | Self::FieldAccess { .. } => (),
      Self::Unary(ref op) if matches!(&**op, UnaryExpr { op: UnaryOp::AddrOf, .. }) => (),
      _ => return Ok((tokens, factor)),
    }

    enum Access {
      Fn(Vec<Expr>),
      Field { field: Identifier, deref: bool },
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
            map(preceded(terminated(token("."), meta), |tokens| Identifier::parse(tokens, ctx)), |field| {
              Access::Field { field, deref: false }
            }),
            map(preceded(terminated(token("->"), meta), |tokens| Identifier::parse(tokens, ctx)), |field| {
              Access::Field { field, deref: true }
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
              (Self::Variable { name }, Access::Fn(args)) => Self::FunctionCall(FunctionCall { name, args }),
              // Field access cannot be chained after postfix `++`/`--`.
              (acc, Access::Field { field, deref }) if !was_unary_op || deref => {
                let acc = if deref { Self::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: acc })) } else { acc };
                Self::FieldAccess { expr: Box::new(acc), field }
              },
              _ => return Err(()),
            },
            is_unary_op,
          ))
        },
      ),
      |res| res.map(|(expr, _)| expr),
    )(tokens)
  }

  fn parse_term_prec2<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec3<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec4<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec5<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec6<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec7<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec8<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, term) = Self::parse_term_prec7(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("&"), meta), |tokens| Self::parse_term_prec7(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitAnd, rhs })),
    )(tokens)
  }

  fn parse_term_prec9<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, term) = Self::parse_term_prec8(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("^"), meta), |tokens| Self::parse_term_prec8(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitXor, rhs })),
    )(tokens)
  }

  fn parse_term_prec10<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    let (tokens, term) = Self::parse_term_prec9(tokens, ctx)?;

    fold_many0(
      preceded(delimited(meta, token("|"), meta), |tokens| Self::parse_term_prec9(tokens, ctx)),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitOr, rhs })),
    )(tokens)
  }

  fn parse_term_prec13<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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

  fn parse_term_prec14<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
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
  pub(crate) fn parse<'i, 'p, I, C>(tokens: &'i [I], ctx: &'p ParseContext<'_>) -> IResult<&'i [I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter<Item = C>
      + InputTakeAtPosition<Item = C>
      + Slice<RangeFrom<usize>>
      + Slice<RangeTo<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + ParseTo<f64>
      + ParseTo<f32>
      + Offset
      + Clone,
    C: AsChar + Copy,
    &'static str: FindToken<<I as InputIter>::Item>,
  {
    Self::parse_term_prec14(tokens, ctx)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    match self {
      Self::Cast { expr, ty } => {
        // Handle ambiguous cast vs. binary operation, e.g. `(ty)&var` vs `(var1) & var2`.
        if let (Self::Unary(expr), Type::Identifier { name: Identifier::Literal(name), is_struct: false }) =
          (&**expr, &ty)
        {
          // Cannot resolve type, so treat this as a binary operation.
          if ctx.resolve_ty(name.as_str()).is_none() {
            let op = match expr.op {
              UnaryOp::Plus => Some(BinaryOp::Add),
              UnaryOp::Minus => Some(BinaryOp::Sub),
              UnaryOp::Deref => Some(BinaryOp::Mul),
              UnaryOp::AddrOf => Some(BinaryOp::BitAnd),
              _ => None,
            };

            if let Some(op) = op {
              let lhs = Self::Variable { name: Identifier::Literal(name.clone()) };
              let rhs = expr.expr.clone();

              *self = Self::Binary(Box::new(BinaryExpr { lhs, op, rhs }));
              return self.finish(ctx)
            }
          }
        }

        expr.finish(ctx)?;
        ty.finish(ctx)?;
        Ok(Some(ty.clone()))
      },
      Self::Variable { ref mut name } => {
        let ty = name.finish(ctx)?;

        if let Identifier::Literal(name) = name {
          let name = name.as_str();

          if let Some(arg_ty) = ctx.arg_type_mut(name) {
            if let MacroArgType::Known(arg_ty) = arg_ty {
              return Ok(Some(arg_ty.clone()))
            }
          } else if let Some(arg_value) = ctx.arg_value(name) {
            *self = arg_value.clone();

            // We are inside a function call evaluation, so the type cannot be evaluated yet.
            return Ok(None)
          } else {
            // Expand variable-like macro.
            match ctx.eval_variable(name) {
              Ok((expr, ty)) => {
                *self = expr;
                return Ok(ty)
              },
              Err(err) => {
                // Built-in macros.
                return match name {
                  "__SCHAR_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::SChar))),
                  "__SHRT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Short))),
                  "__INT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Int))),
                  "__LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Long))),
                  "__LONG_LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::LongLong))),
                  _ => Err(err),
                }
              },
            }
          }
        }

        Ok(ty)
      },
      Self::FunctionCall(call) => {
        if let Identifier::Literal(id) = &call.name {
          if ctx.names.contains(id.as_str()) {
            return Err(crate::Error::RecursiveDefinition(id.as_str().to_owned()))
          }
        }

        let ty = call.finish(ctx)?;

        if let Identifier::Literal(id) = &call.name {
          if !id.macro_arg {
            if let Some(fn_macro) = ctx.function_macro(id.as_str()) {
              let fn_macro = fn_macro.clone();
              match fn_macro.call(&ctx.root_name, &ctx.names, &call.args, ctx)? {
                MacroBody::Statement(_) => return Err(crate::Error::UnsupportedExpression),
                MacroBody::Expr(expr) => {
                  *self = expr;
                  return self.finish(ctx)
                },
              }
            }
          }
        }

        // Type should only be set if calling an actual function, not a function macro.
        Ok(ty)
      },
      Self::Literal(lit) => lit.finish(ctx),
      Self::FieldAccess { expr, field } => {
        expr.finish(ctx)?;
        field.finish(ctx)?;

        if let Identifier::Literal(id) = &field {
          if id.macro_arg {
            if let Some(arg_type) = ctx.arg_type_mut(id.as_str()) {
              *arg_type = MacroArgType::Ident;
            }

            if let Some(expr) = ctx.arg_value(id.as_str()) {
              match expr {
                Self::Variable { name } => {
                  *field = name.clone();
                  return self.finish(ctx)
                },
                _ => return Err(crate::Error::UnsupportedExpression),
              }
            }
          } else if let Some(expr) = ctx.variable_macro_value(id.as_str()) {
            match expr {
              Self::Variable { name } => {
                *field = name.clone();
                return self.finish(ctx)
              },
              _ => return Err(crate::Error::UnsupportedExpression),
            }
          }
        }

        Ok(None)
      },
      Self::Stringify(stringify) => stringify.finish(ctx),
      Self::Concat(names) => {
        let mut new_names = vec![];
        let mut current_name: Option<Vec<u8>> = None;

        for name in &mut *names {
          name.finish(ctx)?;

          if let Self::Literal(Lit::String(LitString { repr })) = name {
            if let Some(ref mut current_name) = current_name {
              current_name.extend_from_slice(repr);
            } else {
              current_name = Some(repr.clone());
            }
          } else {
            if let Some(current_name) = current_name.take() {
              new_names.push(Self::Literal(Lit::String(LitString { repr: current_name })));
            }

            new_names.push(name.clone());
          }
        }

        if let Some(current_name) = current_name.take() {
          new_names.push(Self::Literal(Lit::String(LitString { repr: current_name })));
        }

        if new_names.len() == 1 {
          *self = new_names.remove(0);
          self.finish(ctx)
        } else {
          *self = Self::Concat(new_names);
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
            *self = Self::Literal(Lit::Int(LitInt { value: if *i == 0 { 1 } else { 0 }, suffix: None }));
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
            return Err(crate::Error::UnsupportedExpression)
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
          let prefix = ctx.trait_prefix();

          if *mutable {
            quote! { #prefix ptr::null_mut() }
          } else {
            quote! { #prefix ptr::null() }
          }
        },
        (ty, expr) => {
          if ty.is_void() {
            let expr = expr.to_token_stream(ctx);
            quote! { { drop(#expr) } }
          } else {
            let (prec, _) = self.precedence();
            let (expr_prec, _) = expr.precedence();

            let mut expr = expr.to_token_stream(ctx);
            if expr_prec > prec {
              expr = quote! { (#expr) };
            }

            let ty = ty.to_token_stream(ctx);
            quote! { #expr as #ty }
          }
        },
      }),
      Self::Variable { ref name } => {
        if let Identifier::Literal(name) = name {
          let prefix = &ctx.ffi_prefix();

          match name.as_str() {
            "__SCHAR_MAX__" => return tokens.append_all(quote! { #prefix c_schar::MAX }),
            "__SHRT_MAX__" => return tokens.append_all(quote! { #prefix c_short::MAX }),
            "__INT_MAX__" => return tokens.append_all(quote! { #prefix c_int::MAX }),
            "__LONG_MAX__" => return tokens.append_all(quote! { #prefix c_long::MAX }),
            "__LONG_LONG_MAX__" => return tokens.append_all(quote! { #prefix c_longlong::MAX }),
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
      Self::Stringify(stringify) => {
        stringify.to_tokens(ctx, tokens);
      },
      Self::Concat(ref names) => {
        let ffi_prefix = ctx.ffi_prefix();
        let trait_prefix = ctx.trait_prefix();

        let names = names
          .iter()
          .map(|e| match e {
            Self::Stringify(s) => {
              let id = s.id.to_token_stream(ctx);

              quote! { #trait_prefix stringify!(#id) }
            },
            e => e.to_token_stream(ctx),
          })
          .collect::<Vec<_>>();

        tokens.append_all(quote! {
          {
            const BYTES: &[u8] = #trait_prefix concat!(#(#names),*, '\0').as_bytes();
            BYTES.as_ptr() as *const #ffi_prefix c_char
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
    assert_eq!(expr, lit!('a'));

    let (_, expr) = Expr::parse(&["U'🍩'"], &CTX).unwrap();
    assert_eq!(expr, lit!('🍩'));
  }

  #[test]
  fn parse_stringify() {
    let ctx = ParseContext::fn_macro("EXPR", &["a"]);
    let (_, expr) = Expr::parse(&["#", "a"], &ctx).unwrap();
    assert_eq!(expr, Expr::Stringify(Stringify { id: id!(@a) }));
  }

  #[test]
  fn parse_concat() {
    let (_, expr) = Expr::parse(&[r#""abc""#, r#""def""#], &CTX).unwrap();
    assert_eq!(expr, Expr::Literal(Lit::String(LitString { repr: "abcdef".into() })));

    let ctx = ParseContext::fn_macro("EXPR", &["a"]);
    let (_, expr) = Expr::parse(&[r#""def""#, "#", "a"], &ctx).unwrap();
    assert_eq!(
      expr,
      Expr::Concat(vec![
        Expr::Literal(Lit::String(LitString { repr: "def".into() })),
        Expr::Stringify(Stringify { id: id!(@a) }),
      ])
    );
  }

  #[test]
  fn parse_access() {
    let (_, expr) = Expr::parse(&["a", ".", "b"], &CTX).unwrap();
    assert_eq!(expr, Expr::FieldAccess { expr: Box::new(var!(a)), field: id!(b) });
  }

  #[test]
  fn parse_ptr_access() {
    let (_, expr) = Expr::parse(&["a", "->", "b"], &CTX).unwrap();
    assert_eq!(
      expr,
      Expr::FieldAccess {
        expr: Box::new(Expr::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: var!(a) }))),
        field: id!(b)
      }
    );
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
    assert_eq!(expr, Expr::FunctionCall(FunctionCall { name: id!(my_function), args: vec![var!(arg1), var!(arg2)] }));
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
