use quote::TokenStreamExt;

use super::*;

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'t> {
  Variable { name: Identifier },
  FunctionCall(FunctionCall<'t>),
  Cast { expr: Box<Expr<'t>>, ty: Type },
  Literal(Lit),
  FieldAccess { expr: Box<Self>, field: Identifier },
  Stringify(Stringify),
  Concat(Vec<Expr<'t>>),
  UnaryOp { op: &'t str, expr: Box<Self>, prefix: bool },
  BinOp(Box<Self>, &'t str, Box<Self>),
  Ternary(Box<Self>, Box<Self>, Box<Self>),
  Asm(Asm<'t>),
}

impl<'t> Expr<'t> {
  fn parse_concat<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
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

  fn parse_factor<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    alt((
      Self::parse_concat,
      map(Lit::parse, Self::Literal),
      map(Identifier::parse, |id| Self::Variable { name: id }),
      delimited(pair(token("("), meta), Self::parse, pair(meta, token(")"))),
    ))(tokens)
  }

  fn parse_term_prec1<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, factor) = Self::parse_factor(tokens)?;

    let (tokens, arg) = match factor {
      arg @ Expr::Variable { .. } | arg @ Expr::FunctionCall(..) |
      arg @ Expr::FieldAccess { .. } | arg @ Expr::UnaryOp { op: "&", .. } => {
        enum Access<'t> {
          Fn(Vec<Expr<'t>>),
          Field { field: Identifier, deref: bool },
        }

        if matches!(arg, Expr::Variable { name: Identifier::Literal(ref id) } if id == "__asm") {
          if let Ok((tokens, asm)) = preceded(opt(token("volatile")), Asm::parse)(tokens) {
            return Ok((tokens, Expr::Asm(asm)))
          }
        }

        let (tokens, arg) = fold_many0(
          alt((
            map(
              delimited(
                pair(token("("), meta),
                separated_list0(tuple((meta, token(","), meta)), Self::parse),
                pair(meta, token(")")),
              ),
              |args| Access::Fn(args)
            ),
            map(
              pair(alt((token("."), token("->"))), Identifier::parse),
              |(access, field)| Access::Field { field, deref: access == "->" },
            ),
          )),
          move || arg.clone(),
          |acc, access| match (acc, access) {
            (Expr::Variable { name }, Access::Fn(args)) => Expr::FunctionCall(FunctionCall { name, args }),
            (acc, Access::Field { field, deref }) => {
              let acc = if deref {
                Expr::UnaryOp { op: "*", expr: Box::new(acc), prefix: true }
              } else {
                acc
              };

              Expr::FieldAccess { expr: Box::new(acc), field }
            },
            _ => unimplemented!(),
          },
        )(tokens)?;

        if let Ok((tokens, op)) = alt((token("++"), token("--")))(tokens) {
          (tokens, Expr::UnaryOp { op, expr: Box::new(arg), prefix: false })
        } else {
          (tokens, arg)
        }
      },
      arg => (tokens, arg),
    };

    Ok((tokens, arg))
  }

  fn parse_term_prec2<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    alt((
      map(
        pair(
          delimited(
            pair(token("("), meta),
            Type::parse,
            pair(meta, token(")")),
          ),
          Self::parse_term_prec2,
        ),
        |(ty, term)| {
          // TODO: Handle constness.
          Expr::Cast { expr: Box::new(term), ty }
        },
      ),
      map(
        pair(
          alt((
            token("&"),
            token("++"), token("--"),
            token("+"), token("-"),
            token("!"), token("~"),
          )),
          Self::parse_term_prec2,
        ),
        |(op, term)| {
          Expr::UnaryOp { op, expr: Box::new(term), prefix: true }
        }
      ),
      Self::parse_term_prec1,
    ))(tokens)
  }

  fn parse_term_prec3<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, factor) = Self::parse_term_prec2(tokens)?;

    fold_many0(
      pair(alt((token("*"), token("/"))), Self::parse_term_prec2),
      move || factor.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  fn parse_term_prec4<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec3(tokens)?;

    fold_many0(
      pair(alt((token("+"), token("-"))), Self::parse_term_prec3),
      move || term.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  fn parse_term_prec5<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec4(tokens)?;

    fold_many0(
      pair(alt((token("<<"), token(">>"))), Self::parse_term_prec4),
      move || term.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  fn parse_term_prec6<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec5(tokens)?;

    fold_many0(
      pair(alt((token("<"), token("<="), token(">"), token(">="))), Self::parse_term_prec5),
      move || term.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  fn parse_term_prec7<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec6(tokens)?;

    fold_many0(
      pair(alt((token("=="), token("!="))), Self::parse_term_prec6),
      move || term.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  fn parse_term_prec13<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
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

  fn parse_term_prec14<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, term) = Self::parse_term_prec13(tokens)?;

    fold_many0(
      pair(
        alt((
          token("="),
          token("+="), token("-="),
          token("*="), token("/="), token("%="),
          token("<<="), token(">>="),
          token("&="), token("^="), token("|="),
        )),
        Self::parse_term_prec14,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| {
        Self::BinOp(Box::new(lhs), op, Box::new(rhs))
      }
    )(tokens)
  }

  pub fn parse<'i>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    Self::parse_term_prec14(tokens)
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    match self {
      Self::Cast { expr, ty } => {
        expr.visit(ctx);
        ty.visit(ctx);
      },
      Self::Variable { name } => name.visit(ctx),
      Self::FunctionCall(call) => call.visit(ctx),
      Self::Literal(_) => (),
      Self::FieldAccess { expr, field } => {
        expr.visit(ctx);
        field.visit(ctx);
      },
      Self::Stringify(stringify) => stringify.visit(ctx),
      Self::Concat(names) => {
        for name in names {
          name.visit(ctx);
        }
      },
      Self::UnaryOp { expr, .. } => {
        expr.visit(ctx);
      },
      Self::BinOp(lhs, _, rhs) => {
        lhs.visit(ctx);
        rhs.visit(ctx);
      },
      Self::Ternary(cond, if_branch, else_branch) => {
        cond.visit(ctx);
        if_branch.visit(ctx);
        else_branch.visit(ctx);
      },
      Self::Asm(asm) => asm.visit(ctx),
    }
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
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
        name.to_tokens(ctx, tokens)
      },
      Self::FunctionCall(ref call) => {
        call.to_tokens(ctx, tokens);
      },
      Self::Literal(ref lit) => {
        tokens.append_all(Some(lit))
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
      Self::UnaryOp { ref op, ref expr, prefix } => {
        let expr = expr.to_token_stream(ctx);

        tokens.append_all(match (*op, prefix) {
          ("++", true) => quote! { { #expr += 1; #expr } },
          ("--", true) => quote! { { #expr -= 1; #expr } },
          ("++", false) => quote! { { let prev = #expr; #expr += 1; prev } },
          ("--", false) => quote! { { let prev = #expr; #expr -= 1; prev } },
          ("!", _) => quote! { (#expr == Default::default()) },
          ("~", _) => quote! { (!#expr) },
          ("+", _) => quote! { (+#expr) },
          ("-", _) => quote! { (-#expr) },
          ("*", true) => quote! { (*#expr) },
          ("&", true) => quote! { ::core::ptr::addr_of_mut!(#expr) },
          (op, _) => todo!("op = {:?}", op),
        })
      },
      Self::BinOp(ref lhs, ref op, ref rhs) => {
        let lhs = lhs.to_token_stream(ctx);
        let rhs = rhs.to_token_stream(ctx);

        tokens.append_all(match *op {
          "="  => quote! { { #lhs  = #rhs; #lhs } },
          "+=" => quote! { { #lhs += #rhs; #lhs } },
          "-=" => quote! { { #lhs -= #rhs; #lhs } },
          "&=" => quote! { { #lhs &= #rhs; #lhs } },
          "|=" => quote! { { #lhs |= #rhs; #lhs } },
          "^=" => quote! { { #lhs ^= #rhs; #lhs } },
          "==" => quote! { ( #lhs == #rhs ) },
          "!=" => quote! { ( #lhs != #rhs ) },
          "+"  => quote! { ( #lhs +  #rhs ) },
          "-"  => quote! { ( #lhs -  #rhs ) },
          "*"  => quote! { ( #lhs *  #rhs ) },
          "/"  => quote! { ( #lhs /  #rhs ) },
          "&"  => quote! { ( #lhs &  #rhs ) },
          "|"  => quote! { ( #lhs |  #rhs ) },
          "^"  => quote! { ( #lhs ^  #rhs ) },
          "<=" => quote! { ( #lhs <= #rhs ) },
          "<"  => quote! { ( #lhs <  #rhs ) },
          ">"  => quote! { ( #lhs >  #rhs ) },
          ">=" => quote! { ( #lhs >= #rhs ) },
          op   => todo!("op {:?}", op),
        });
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

  pub fn to_token_stream(&self, ctx: &mut Context) -> TokenStream {
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
    assert_eq!(expr, Expr::Concat(vec![
      Expr::Literal(Lit::String(LitString { repr: "abc".into() })),
      Expr::Literal(Lit::String(LitString { repr: "def".into() })),
    ]));

    let (_, expr) = Expr::parse(&[r#""def""#, "#", "a"]).unwrap();
    assert_eq!(expr, Expr::Concat(vec![
      Expr::Literal(Lit::String(LitString { repr: "def".into() })),
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
      expr: Box::new(Expr::UnaryOp { op: "*", expr: Box::new(var!(a)), prefix: true }),
      field: id!(b),
    });
  }

  #[test]
  fn parse_assignment() {
    let (_, expr) = Expr::parse(&["a", "=", "b", "=", "c"]).unwrap();
    assert_eq!(expr, Expr::BinOp(
      Box::new(var!(a)),
      "=",
      Box::new(Expr::BinOp(
        Box::new(var!(b)),
        "=",
        Box::new(var!(c)),
      ))
    ));
  }
}
