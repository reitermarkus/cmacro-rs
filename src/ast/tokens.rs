use std::{borrow::Cow, fmt::Debug, ops::RangeFrom};

use nom::{
  bytes::complete::{tag, take_until},
  combinator::{all_consuming, map_opt, map_parser, opt, value},
  multi::many0,
  sequence::{delimited, pair, preceded},
  Compare, FindSubstring, IResult, InputLength, InputTake, Parser, Slice,
};

use crate::MacroToken;

pub(crate) fn macro_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], usize> {
  map_opt(take_one_ref, |token| if let MacroToken::Arg(index) = token { Some(*index) } else { None })(tokens)
}

pub(crate) fn macro_token<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Cow<'t, str>> {
  map_opt(take_one_ref, |token| {
    let token = if let MacroToken::Token(token) = token { token } else { return None };
    Some(token.clone())
  })(tokens)
}

pub(crate) fn take_one_ref<I>(tokens: &[I]) -> IResult<&[I], &I>
where
  I: Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn take_one<I>(tokens: &[I]) -> IResult<&[I], I>
where
  I: Debug + Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first.clone()))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<I>(tokens: &[I]) -> IResult<&[I], I>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone,
{
  let (tokens, token) = take_one(tokens)?;

  let (_, comment) = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))?;

  Ok((tokens, comment))
}

pub(crate) fn meta<I>(input: &[I]) -> IResult<&[I], Vec<I>>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone,
{
  many0(comment)(input)
}

pub(crate) fn token<I>(token: &'static str) -> impl Fn(&[I]) -> IResult<&[I], &'static str>
where
  I: Debug + InputTake + InputLength + Slice<RangeFrom<usize>> + Compare<&'static str> + Clone,
{
  move |tokens| {
    map_parser(take_one, |token2| {
      all_consuming(preceded(opt(tag("\\\n")), value(token, tag(token))))(token2)
        .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))
    })(tokens)
  }
}

pub(crate) use token as keyword;

pub(crate) fn parenthesized<'i, I, O, F>(f: F) -> impl FnMut(&'i [I]) -> IResult<&'i [I], O, nom::error::Error<&'i [I]>>
where
  I: Debug
    + InputTake
    + InputLength
    + Slice<std::ops::RangeFrom<usize>>
    + Compare<&'static str>
    + FindSubstring<&'static str>
    + Clone
    + 'i,
  F: Parser<&'i [I], O, nom::error::Error<&'i [I]>>,
{
  delimited(pair(token("("), meta), f, pair(meta, token(")")))
}
