use nom::{
  bytes::complete::{tag, take_until},
  combinator::{all_consuming, map_opt, map_parser, opt, value},
  multi::many0,
  sequence::{delimited, pair, preceded},
  IResult, Parser,
};

use crate::MacroToken;

pub(crate) fn macro_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], usize> {
  map_opt(take_one, |token| if let MacroToken::Arg(index) = token { Some(*index) } else { None })(tokens)
}

pub(crate) fn macro_token<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'i str> {
  map_opt(take_one, |token| {
    let token = if let MacroToken::Token(token) = token { token } else { return None };
    Some(token.as_ref())
  })(tokens)
}

pub(crate) fn take_one<I>(tokens: &[I]) -> IResult<&[I], &I>
where
  I: Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'i str> {
  map_parser(macro_token, |token: &'i str| {
    all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token)
      .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))
  })(tokens)
}

pub(crate) fn meta<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Vec<&'i str>> {
  many0(comment)(input)
}

pub(crate) fn token<'i, 't>(
  token: &'static str,
) -> impl Fn(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str>
where
  't: 'i,
{
  move |tokens| {
    map_parser(macro_token, |token2: &'i str| {
      all_consuming(preceded(opt(tag("\\\n")), value(token, tag(token))))(token2)
        .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

      Ok(("", token))
    })(tokens)
  }
}

pub(crate) use token as keyword;

pub(crate) fn parenthesized<'i, 't, O, F>(
  f: F,
) -> impl FnMut(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>
where
  't: 'i,
  F: Parser<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>,
{
  delimited(pair(token("("), meta), f, pair(meta, token(")")))
}
