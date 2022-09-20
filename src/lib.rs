use std::fmt::{self, Write};
use std::collections::HashMap;
use std::str;

use quote::quote;
use proc_macro2::{TokenStream, Ident, Span};

use nom::multi::{separated_list0};
use nom::branch::alt;
use nom::combinator::map;
use nom::sequence::delimited;
use nom::sequence::terminated;
use nom::combinator::{opt, eof};
use nom::sequence::tuple;
use nom::IResult;
use nom::multi::{many0, fold_many0};
use nom::sequence::pair;
use nom::sequence::preceded;
use nom::branch::permutation;
use nom::multi::many0_count;

mod asm;
pub use asm::*;

mod ty;
pub use ty::*;

mod identifier;
pub use identifier::*;

mod expr;
pub use expr::*;

mod function_call;
pub use function_call::*;

mod function_decl;
pub use function_decl::*;

mod literal;
pub(crate) use literal::*;

mod statement;
pub(crate) use statement::*;

mod decl;
pub(crate) use decl::*;

mod stringify;
pub(crate) use stringify::*;

fn comment<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {
  if let Some(token) = tokens.get(0) {
    if token.starts_with("/*") && token.ends_with("*/") {
      return Ok((&tokens[1..], token))
    }
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
}

fn meta<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Vec<&'t str>> {
  many0(comment)(input)
}

fn token<'i, 't>(token: &'static str) -> impl Fn(&'i [&'t str]) -> IResult<&'i [&'t str], &'t str>
where
  't: 'i,
{
  move |tokens: &[&str]| {
    if let Some(token2) = tokens.get(0).as_deref() {
      let token2 = if token2.starts_with("\\\n") { // TODO: Fix in tokenizer/lexer.
        &token2[2..]
      } else {
        token2
      };

      if token2 == token {
        return Ok((&tokens[1..], token2))
      }
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
  }
}

/// Type of a macro argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroArgType {
  /// `ident` type
  Ident,
  /// `expr` type
  Expr,
  Unknown,
}

#[derive(Debug)]
pub struct Context<'s, 'f> {
  args: HashMap<&'s str, MacroArgType>,
  export_as_macro: bool,
  functions: HashMap<&'f str, Vec<String>>,
}

impl<'s, 't> Context<'s, 't> {
  pub fn is_macro_arg(&self, name: &str) -> bool {
    self.args.get(name).map(|&ty| self.export_as_macro || ty != MacroArgType::Unknown).unwrap_or(false)
  }
}

#[derive(Debug)]
pub struct FnMacro<'t> {
  pub name: &'t str,
  pub args: Vec<(&'t str, MacroArgType)>,
  pub body: MacroBody<'t>,
}

impl<'t> FnMacro<'t> {
  pub fn parse<'i>(sig: &'t str, body: &'i [&'t str]) -> Result<Self, ()> {
    let sig = tokenize_name(sig.as_bytes());

    let (_, sig) = MacroSig::parse(&sig).unwrap();

    let mut args = HashMap::new();
    for &arg in &sig.arguments {
      args.insert(arg, MacroArgType::Unknown);
    }

    let (_, mut body) = MacroBody::parse(&body).unwrap();

    let mut ctx = Context { args, export_as_macro: false, functions: HashMap::new() };
    body.visit(&mut ctx);

    let args = sig.arguments.into_iter().map(|a| (a, ctx.args.remove(a).unwrap())).collect();
    Ok(Self { name: sig.name, args, body })
  }

  pub fn write(
    &self,
    f: &mut String,
    mut variable_type: impl FnMut(&str, &str) -> Option<syn::Type>,
    mut return_type: impl FnMut(&str) -> Option<syn::Type>,
  ) -> fmt::Result {
    let mut export_as_macro = !self.args.iter().all(|&(_, ty)| ty == MacroArgType::Unknown);
    let func_args = self.args.iter().filter_map(|&(arg, _)| {
      let id = Ident::new(arg, Span::call_site());
      if let Some(ty) = variable_type(self.name, arg) {
        Some(quote! { #id: #ty })
      } else {
        None
      }
    }).collect::<Vec<_>>();

    if func_args.len() != self.args.len() {
      export_as_macro = true;
    }

    let mut args = HashMap::new();
    for &(arg, ty) in &self.args {
      args.insert(arg, ty);
    }
    let mut ctx = Context { args, export_as_macro, functions: HashMap::new() };

    let name = Ident::new(self.name, Span::call_site());

    let mut body = TokenStream::new();
    match &self.body {
      MacroBody::Block(stmt) => stmt.to_tokens(&mut ctx, &mut body),
      MacroBody::Expr(expr) => expr.to_tokens(&mut ctx, &mut body),
    }

    if export_as_macro {
      let args = self.args.iter().map(|&(arg, ty)| {
        let id = Ident::new(arg, Span::call_site());

        if ty == MacroArgType::Ident {
          quote! { $#id:ident }
        } else {
          quote! { $#id:expr }
        }
      }).collect::<Vec<_>>();

      write!(f, "{}", quote! {
        macro_rules! #name {
          (#(#args),*) => {
            #body
          };
        }
      })
    } else {
      let return_type = return_type(&self.name).map(|ty| {
        quote! { -> #ty }
      });

      let semicolon = if return_type.is_none() {
        Some(quote! { ; })
      } else {
        None
      };

      writeln!(f, "{}", quote! {
        #[allow(non_snake_case)]
        #[inline(always)]
        pub unsafe extern "C" fn #name(#(mut #func_args),*) #return_type {
          #body
          #semicolon
        }
      })
    }
  }
}

/// The signature of a macro.
#[derive(Debug)]
pub struct MacroSig<'t> {
  pub name: &'t str,
  pub arguments: Vec<&'t str>,
}

fn tokenize_name(input: &[u8]) -> Vec<&str> {
  let mut tokens = vec![];

  let mut i = 0;

  loop {
    match input.get(i) {
      Some(b'a'..=b'z' | b'A'..=b'Z' | b'_') => {
        let start = i;
        i += 1;

        while let Some(b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'0'..=b'9') = input.get(i) {
          i += 1;
        }

        tokens.push(unsafe { str::from_utf8_unchecked(&input[start..i]) });
      },
      Some(b'(' | b')' | b',') => {
        tokens.push(unsafe { str::from_utf8_unchecked(&input[i..(i + 1)]) });
        i += 1;
      },
      Some(b'/') if matches!(input.get(i + 1), Some(b'*')) => {
        let start = i;
        i += 2;

        while let Some(c) = input.get(i) {
          i += 1;

          if *c == b'*' {
            if let Some(b'/') = input.get(i) {
              i += 1;
              tokens.push(unsafe { str::from_utf8_unchecked(&input[start..i]) });
              break;
            }
          }
        }
      },
      Some(b'.') if matches!(input.get(i..(i + 3)), Some(b"...")) => {
        tokens.push(unsafe { str::from_utf8_unchecked(&input[i..(i + 3)]) });
        i += 3;
      },
      Some(b' ') => {
        i += 1;
      },
      Some(c) => unreachable!("{}", *c as char),
      None => break,
    }
  }

  tokens
}

impl<'t> MacroSig<'t> {
  pub fn parse<'i>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (input, name) = identifier(input)?;

    let (input, arguments) = terminated(
      delimited(
        pair(token("("), meta),
        alt((
          map(
            token("..."),
            |var_arg| vec![var_arg],
          ),
          map(
            tuple((
              separated_list0(tuple((meta, token(","), meta)), identifier),
              opt(tuple((tuple((meta, token(","), meta)), token("...")))),
            )),
            |(arguments, var_arg)| {
              let mut arguments = arguments.to_vec();

              if let Some((_, var_arg)) = var_arg {
                arguments.push(var_arg);
              }

              arguments
            },
          ),
        )),
        pair(meta, token(")")),
      ),
      eof,
    )(input)?;
    assert!(input.is_empty());

    Ok((input, MacroSig { name, arguments }))
  }
}

/// The body of a macro.
#[derive(Debug)]
pub enum MacroBody<'t> {
  Block(Statement<'t>),
  Expr(Expr<'t>),
}

impl<'t> MacroBody<'t> {
  pub fn parse<'i>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (input, _) = meta(input)?;

    if input.is_empty() {
      return Ok((input, MacroBody::Block(Statement::Block(vec![]))))
    }

    let (input, body) = alt((
      terminated(map(Expr::parse, MacroBody::Expr), eof),
      terminated(map(Statement::parse, MacroBody::Block), eof),
    ))(input)?;
    assert!(input.is_empty());

    Ok((input, body))
  }

  pub fn visit<'s, 'v>(&mut self, ctx: &mut Context<'s, 'v>) {
    match self {
      Self::Block(stmt) => stmt.visit(ctx),
      Self::Expr(expr) => expr.visit(ctx),
    }
  }
}
