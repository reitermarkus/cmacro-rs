use nom::bytes::complete::tag;
use nom::bytes::complete::take_until;
use nom::combinator::all_consuming;
use nom::combinator::map_opt;
use nom::multi::many0;
use nom::sequence::delimited;
use nom::sequence::pair;
use nom::Compare;
use nom::CompareResult;
use nom::FindSubstring;
use nom::IResult;
use nom::InputLength;
use nom::InputTake;
use nom::Parser;

pub(crate) fn take_one<'i, 't, I>(tokens: &'i [I]) -> IResult<&'i [I], I>
where
  I: Clone + 't,
  'i: 't,
{
  if tokens.len() > 0 {
    return Ok((&tokens[1..], tokens[0].clone()))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<'i, 't, I>(tokens: &'i [I]) -> IResult<&'i [I], I>
where
  I: InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone + 't,
  'i: 't,
{
  let (tokens, token) = take_one(tokens)?;

  let (_, comment) = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))?;

  Ok((tokens, comment))
}

pub(crate) fn meta<'i, 't, I>(input: &'i [I]) -> IResult<&'i [I], Vec<I>>
where
  I: InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone + 't,
  'i: 't,
{
  many0(comment)(input)
}

pub(crate) fn token<'i, 't, I>(token: &'static str) -> impl Fn(&'i [I]) -> IResult<&'i [I], &'static str>
where
  I: InputTake + InputLength + Compare<&'static str> + Clone + 't,
  'i: 't,
{
  move |tokens: &[I]| {
    map_opt(take_one, |token2: I| {
      let token2 = if token2.input_len() >= 2 && token2.take(2).compare("\\\n") == CompareResult::Ok {
        // TODO: Fix in tokenizer/lexer.
        let (_, token2) = token2.take_split(2);
        token2
      } else {
        token2
      };

      if token2.compare(token) == CompareResult::Ok {
        Some(token)
      } else {
        None
      }
    })(tokens)
  }
}

pub(crate) use token as keyword;

pub(crate) fn parenthesized<'i, 't, I, O, F>(
  f: F,
) -> impl FnMut(&'i [I]) -> IResult<&'i [I], O, nom::error::Error<&'i [I]>>
where
  I: InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone + 'i,
  O: 'i,
  F: Parser<&'i [I], O, nom::error::Error<&'i [I]>>,
  'i: 't,
{
  delimited(pair(token("("), meta), f, pair(meta, token(")")))
}
