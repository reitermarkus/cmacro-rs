use quote::TokenStreamExt;
use nom::IResult;
use nom::multi::fold_many0;
use quote::quote;

use crate::tokens::parenthesized;
use super::*;

/// An expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
  Variable { name: Identifier },
  FunctionCall(FunctionCall),
  Cast { expr: Box<Expr>, ty: Type },
  Literal(Lit),
  FieldAccess { expr: Box<Self>, field: Identifier },
  Stringify(Stringify),
  Concat(Vec<Expr>),
  UnaryOp(Box<UnaryOp>),
  BinOp(Box<BinaryOp>),
  Ternary(Box<Self>, Box<Self>, Box<Self>),
  Asm(Asm),
}

impl Expr {
  fn parse_concat<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let mut parse_string = alt((
      map(LitString::parse, |s| Self::Literal(Lit::String(s))),
      map(Stringify::parse, Self::Stringify),
    ));

    let (tokens, s) = parse_string(tokens)?;

    fold_many0(
      preceded(meta, parse_string),
      move || s.clone(),
      |mut acc, item| {
        match acc {
          Self::Concat(ref mut args) => {
            args.push(item);
            acc
          },
          acc => Self::Concat(vec![acc, item]),
        }
      }
    )(tokens)
  }

  fn parse_factor<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    alt((
      Self::parse_concat,
      map(Lit::parse, Self::Literal),
      map(Identifier::parse, |id| Self::Variable { name: id }),
      parenthesized(Self::parse),
    ))(tokens)
  }

  fn parse_term_prec1<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, factor) = Self::parse_factor(tokens)?;

    if !(matches!(
      factor,
      Expr::Variable { .. } | Expr::FunctionCall(..) | Expr::FieldAccess { .. },
    ) || matches!(
      factor,
      Expr::UnaryOp(ref op) if matches!(**op, UnaryOp::AddrOf(_)),
    )) {
      return Ok((tokens, factor))
    }

    enum Access {
      Fn(Vec<Expr>),
      Field { field: Identifier, deref: bool },
    }

    if matches!(factor, Expr::Variable { name: Identifier::Literal(ref id) } if id == "__asm") {
      if let Ok((tokens, asm)) = preceded(opt(token("volatile")), Asm::parse)(tokens) {
        return Ok((tokens, Expr::Asm(asm)))
      }
    }

    let fold = fold_many0(
      alt((
        map(
          parenthesized(
            separated_list0(tuple((meta, token(","), meta)), Self::parse),
          ),
          Access::Fn,
        ),
        map(
          pair(alt((token("."), token("->"))), Identifier::parse),
          |(access, field)| Access::Field { field, deref: access == "->" },
        ),
      )),
      move || factor.clone(),
      |acc, access| match (acc, access) {
        (Expr::Variable { name }, Access::Fn(args)) => Expr::FunctionCall(FunctionCall { name, args }),
        (acc, Access::Field { field, deref }) => {
          let acc = if deref {
            Expr::UnaryOp(Box::new(UnaryOp::Deref(acc)))
          } else {
            acc
          };

          Expr::FieldAccess { expr: Box::new(acc), field }
        },
        _ => unimplemented!(),
      },
    );

    map(
      pair(
        fold,
        opt(alt((token("++"), token("--")))),
      ),
      |(expr, op)| match op {
        Some("++") => Expr::UnaryOp(Box::new(UnaryOp::PostInc(expr))),
        Some("--") => Expr::UnaryOp(Box::new(UnaryOp::PostDec(expr))),
        _ => expr,
      }
    )(tokens)
  }

  fn parse_term_prec2<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    alt((
      map(
        pair(
          parenthesized(Type::parse),
          Self::parse_term_prec2,
        ),
        |(ty, term)| {
          // TODO: Handle constness.
          Expr::Cast { expr: Box::new(term), ty }
        },
      ),
      map(
        alt((
          map(preceded(token("&"), Self::parse_term_prec2), UnaryOp::AddrOf),
          map(preceded(token("++"), Self::parse_term_prec2), UnaryOp::Inc),
          map(preceded(token("--"), Self::parse_term_prec2), UnaryOp::Dec),
          map(preceded(token("+"), Self::parse_term_prec2), UnaryOp::Plus),
          map(preceded(token("-"), Self::parse_term_prec2), UnaryOp::Minus),
          map(preceded(token("!"), Self::parse_term_prec2), UnaryOp::Not),
          map(preceded(token("~"), Self::parse_term_prec2), UnaryOp::Comp),
        )),
        |op| {
          Expr::UnaryOp(Box::new(op))
        }
      ),
      Self::parse_term_prec1,
    ))(tokens)
  }

  fn parse_term_prec3<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, factor) = Self::parse_term_prec2(tokens)?;

    fold_many0(
      pair(
        alt((
          token("*"),
          token("/"),
        )),
        Self::parse_term_prec2,
      ),
      move || factor.clone(),
      |lhs, (op, rhs)| {
        if op == "*" {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Mul, rhs }))
        } else {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Div, rhs }))
        }
      }
    )(tokens)
  }

  fn parse_term_prec4<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec3(tokens)?;

    fold_many0(
      pair(
        alt((
          token("+"),
          token("-"),
        )),
        Self::parse_term_prec3,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        if op == "+" {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Plus, rhs }))
        } else {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Minus, rhs }))
        }
      }
    )(tokens)
  }

  fn parse_term_prec5<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec4(tokens)?;

    fold_many0(
      pair(
        alt((
          token("<<"),
          token(">>"),
        )),
        Self::parse_term_prec4,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        if op == "<<" {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Shl, rhs }))
        } else {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Shr, rhs }))
        }
      }
    )(tokens)
  }

  fn parse_term_prec6<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec5(tokens)?;

    fold_many0(
      pair(
        alt((
          token("<"),
          token("<="),
          token(">"),
          token(">="),
        )),
        Self::parse_term_prec5,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        match op {
          "<" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Lt, rhs })),
          "<=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Lte, rhs })),
          ">" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Gt, rhs })),
          ">=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Gte, rhs })),
          _ => unreachable!(),
        }

      }
    )(tokens)
  }

  fn parse_term_prec7<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec6(tokens)?;

    fold_many0(
      pair(
        alt((
          token("=="),
          token("!="),
        )),
        Self::parse_term_prec6,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        if op == "==" {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Eq, rhs }))
        } else {
          Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Neq, rhs }))
        }
      }
    )(tokens)
  }

  fn parse_term_prec13<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec7(tokens)?;

    // Parse ternary.
    if let Ok((tokens, _)) = token("?")(tokens) {
      let (tokens, if_branch) = Self::parse_term_prec7(tokens)?;
      let (tokens, _) = token(":")(tokens)?;
      let (tokens, else_branch) = Self::parse_term_prec7(tokens)?;
      return Ok((tokens, Expr::Ternary(Box::new(term), Box::new(if_branch), Box::new(else_branch))))
    }

    Ok((tokens, term))
  }

  fn parse_term_prec14<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec13(tokens)?;

    fold_many0(
      pair(
        alt((
          token("="),
          token("+="),
          token("-="),
          token("*="),
          token("/="),
          token("%="),
          token("<<="),
          token(">>="),
          token("&="),
          token("^="),
          token("|="),
        )),
        Self::parse_term_prec14,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        match op {
          "=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::Assign, rhs })),
          "+=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::AddAssign, rhs })),
          "-=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::SubAssign, rhs })),
          "*=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::MulAssign, rhs })),
          "/=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::DivAssign, rhs })),
          "%=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::ModAssign, rhs })),
          "<<=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::ShlAssign, rhs })),
          ">>=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::ShrAssign, rhs })),
          "&=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::BitAndAssign, rhs })),
          "^=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::XorAssign, rhs })),
          "|=" => Self::BinOp(Box::new(BinaryOp { lhs, op: BinOp::BitOrAssign, rhs })),
          _ => unreachable!(),
        }
      }
    )(tokens)
  }

  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    Self::parse_term_prec14(tokens)
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    match self {
      Self::Cast { expr, ty } => {
        expr.finish(ctx)?;
        ty.finish(ctx)?;
      },
      Self::Variable { ref mut name } => {
        if let Identifier::Literal(id) = name {
          if let Some(expr) = ctx.macro_variable(id.as_str()) {
            *self = expr.clone();
            return self.finish(ctx);
          }

          // Built-in macros.
          match id.as_str() {
            "__SCHAR_MAX__"
            | "__SHRT_MAX__"
            | "__INT_MAX__"
            | "__LONG_MAX__"
            | "__LONG_LONG_MAX__" => return Ok(()),
            _ => (),
          }
        }

        name.finish(ctx)?;
      },
      Self::FunctionCall(call) => call.finish(ctx)?,
      Self::Literal(_) => (),
      Self::FieldAccess { expr, field } => {
        expr.finish(ctx)?;
        field.finish(ctx)?;
      },
      Self::Stringify(stringify) => stringify.finish(ctx)?,
      Self::Concat(names) => {
        for name in names {
          name.finish(ctx)?;
        }
      },
      Self::UnaryOp(op) => {
        op.finish(ctx)?;

        match &**op {
          UnaryOp::Plus(
            expr @ Expr::Literal(Lit::Int(_)) |
            expr @ Expr::Literal(Lit::Float(_)),
          ) => {
            *self = expr.clone();
          },
          UnaryOp::Minus(Expr::Literal(Lit::Int(LitInt(i)))) => {
            *self = Expr::Literal(Lit::Int(LitInt(i.wrapping_neg())));
          },
          UnaryOp::Minus(Expr::Literal(Lit::Float(f))) => {
            *self = Expr::Literal(Lit::Float(match f {
              LitFloat::Float(f) => LitFloat::Float(-f),
              LitFloat::Double(f) => LitFloat::Double(-f),
              LitFloat::LongDouble(f) => LitFloat::LongDouble(-f),
            }));
          },
          UnaryOp::Not(Expr::Literal(Lit::Int(LitInt(i)))) => {
            *self = Expr::Literal(Lit::Int(LitInt(if *i == 0 { 1 } else { 0 })));
          },
          UnaryOp::Not(Expr::Literal(Lit::Float(f))) => {
            *self = Expr::Literal(Lit::Float(match f {
              LitFloat::Float(f) => LitFloat::Float(if *f == 0.0 { 1.0 } else { 0.0 }),
              LitFloat::Double(f) => LitFloat::Double(if *f == 0.0 { 1.0 } else { 0.0 }),
              LitFloat::LongDouble(f) => LitFloat::LongDouble(if *f == 0.0 { 1.0 } else { 0.0 }),
            }));
          },
          UnaryOp::Comp(Expr::Literal(Lit::Int(LitInt(i)))) => {
            *self = Expr::Literal(Lit::Int(LitInt(!i)));
          },
          UnaryOp::Comp(Expr::Literal(Lit::Float(_) | Lit::String(_))) => {
            return Err(crate::Error::UnsupportedExpression)
          },
          _ => (),
        }
      },
      Self::BinOp(op) => {
        op.finish(ctx)?;
      },
      Self::Ternary(cond, if_branch, else_branch) => {
        cond.finish(ctx)?;
        if_branch.finish(ctx)?;
        else_branch.finish(ctx)?;
      },
      Self::Asm(asm) => asm.finish(ctx)?,
    }

    Ok(())
  }

  pub(crate) fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    match self {
      Self::Cast { ref expr, ref ty } => {
        let expr = expr.to_token_stream(ctx);

        tokens.append_all(if matches!(ty, Type::Identifier { name: Identifier::Literal(id), .. } if id == "void") {
          quote! { { drop(#expr) } }
        } else {
          let ty = ty.to_token_stream(ctx);
          quote! { #expr as #ty }
        })
      },
      Self::Variable { name: Identifier::Literal(id) } if id == "NULL" => {
        tokens.append_all(quote! { ::core::ptr::null_mut() });
      },
      Self::Variable { name: Identifier::Literal(id) } if id == "eIncrement" => {
        tokens.append_all(quote! { eNotifyAction_eIncrement });
      },
      Self::Variable { ref name } => {
        if let Identifier::Literal(id) = name {
          eprintln!("ID = {:?}", id);

          let prefix = &ctx.global_context.ffi_prefix;

          match id.as_str() {
            "__SCHAR_MAX__" => {
              return tokens.append_all(quote!{ #prefix c_schar::MAX })
            },
            "__SHRT_MAX__" => {
              return tokens.append_all(quote!{ #prefix c_short::MAX })
            },
            "__INT_MAX__" => {
              return tokens.append_all(quote!{ #prefix c_int::MAX })
            },
            "__LONG_MAX__" => {
              return tokens.append_all(quote!{ #prefix c_long::MAX })
            },
            "__LONG_LONG_MAX__" => {
              return tokens.append_all(quote!{ #prefix c_longlong::MAX })
            },
            _ => (),
          }
        }

        name.to_tokens(ctx, tokens)
      },
      Self::FunctionCall(ref call) => {
        call.to_tokens(ctx, tokens);
      },
      Self::Literal(ref lit) => {
        lit.to_tokens(ctx, tokens)
      },
      Self::FieldAccess { ref expr, ref field } => {
        let expr = expr.to_token_stream(ctx);
        let field = field.to_token_stream(ctx);

        tokens.append_all(quote! {
          (#expr).#field
        })
      },
      Self::Stringify(stringify) => {
        stringify.to_tokens(ctx, tokens);
      },
      Self::Concat(ref names) => {
        let names = names.iter().map(|e| e.to_token_stream(ctx)).collect::<Vec<_>>();

        tokens.append_all(quote! {
          ::core::concat!(
            #(#names),*
          )
        })
      },
      Self::UnaryOp(op) => {
        op.to_tokens(ctx, tokens)
      },
      Self::BinOp(op) => {
        op.to_tokens(ctx, tokens)
      },
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

  pub(crate) fn to_token_stream(&self, ctx: &mut LocalContext) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! id {
    ($name:ident) => { Identifier::Literal(String::from(stringify!($name))) }
  }

  macro_rules! var {
    ($name:ident) => { Expr::Variable { name: id!($name) } };
  }

  #[test]
  fn parse_stringify() {
    let (_, expr) = Expr::parse(&["#", "a"]).unwrap();
    assert_eq!(expr, Expr::Stringify(Stringify { id: id!(a) }));
  }

  #[test]
  fn parse_concat() {
    let (_, expr) = Expr::parse(&[r#""abc""#, r#""def""#]).unwrap();
    assert_eq!(expr, Expr::Literal(Lit::String(LitString { repr: b"abcdef".to_vec() })));

    let (_, expr) = Expr::parse(&[r#""def""#, "#", "a"]).unwrap();
    assert_eq!(expr, Expr::Concat(vec![
      Expr::Literal(Lit::String(LitString { repr: b"def".to_vec() })),
      Expr::Stringify(Stringify { id: id!(a) }),
    ]));
  }

  #[test]
  fn parse_access() {
    let (_, expr) = Expr::parse(&["a", ".", "b"]).unwrap();
    assert_eq!(expr, Expr::FieldAccess { expr: Box::new(var!(a)), field: id!(b) });
  }

  #[test]
  fn parse_ptr_access() {
    let (_, expr) = Expr::parse(&["a", "->", "b"]).unwrap();
    assert_eq!(expr, Expr::FieldAccess {
      expr: Box::new(Expr::UnaryOp(Box::new(UnaryOp::Deref(var!(a))))),
      field: id!(b),
    });
  }

  #[test]
  fn parse_assignment() {
    let (_, expr) = Expr::parse(&["a", "=", "b", "=", "c"]).unwrap();
    assert_eq!(expr, Expr::BinOp(
      Box::new(BinaryOp {
        lhs: var!(a),
        op: BinOp::Assign,
        rhs: Expr::BinOp(
          Box::new(BinaryOp {
            lhs: var!(b),
            op: BinOp::Assign,
            rhs: var!(c),
          }),
        ),
      })
    ));
  }
}
