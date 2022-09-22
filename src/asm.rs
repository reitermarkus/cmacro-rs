use quote::TokenStreamExt;
use nom::IResult;

use crate::tokens::parenthesized;
use super::*;

/// An inline assemble call.
#[derive(Debug, Clone, PartialEq)]
pub struct Asm {
  template: Vec<LitString>,
  outputs: Vec<Expr>,
  inputs: Vec<Expr>,
  clobbers: Vec<Expr>,
}

impl Asm {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, (template, outputs, inputs, clobbers)) = parenthesized(
      tuple((
        separated_list0(tuple((meta, token(","), meta)), LitString::parse),
        opt(preceded(token(":"), separated_list0(tuple((meta, token(","), meta)), Expr::parse))),
        opt(preceded(token(":"), separated_list0(tuple((meta, token(","), meta)), Expr::parse))),
        opt(preceded(token(":"), separated_list0(tuple((meta, token(","), meta)), Expr::parse))),
      )),
    )(tokens)?;

    let outputs = outputs.unwrap_or_default();
    let inputs = inputs.unwrap_or_default();

    let clobbers = clobbers.unwrap_or_default().into_iter().filter_map(|c| match c {
        Expr::Literal(Lit::String(s)) if s == "memory" => None,
        clobber => Some(clobber),
    }).collect::<Vec<_>>();

    Ok((tokens, Self { template, outputs, inputs, clobbers }))
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    drop(ctx);
    Ok(())
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    let template = &self.template;
    let outputs = self.outputs.iter().map(|o| o.to_token_stream(ctx)).collect::<Vec<_>>();
    let inputs = self.inputs.iter().map(|o| o.to_token_stream(ctx)).collect::<Vec<_>>();
    let clobbers = self.clobbers.iter().map(|o| o.to_token_stream(ctx)).collect::<Vec<_>>();

    tokens.append_all(quote! {
      ::core::arch::asm!(
        #(#template,)*
        #(#outputs,)*
        #(#inputs,)*
        #(out(#clobbers) _,)*
        clobber_abi("C"),
        options(raw)
      )
    })
  }
}
