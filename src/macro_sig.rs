use std::str;

use nom::branch::alt;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::combinator::opt;
use nom::multi::separated_list0;
use nom::sequence::tuple;
use nom::AsChar;
use nom::Compare;
use nom::FindSubstring;
use nom::IResult;
use nom::InputIter;
use nom::InputLength;
use nom::InputTake;

use crate::ast::identifier;
use crate::ast::{meta, parenthesized, token};

/// The signature of a macro.
#[derive(Debug)]
pub struct MacroSig {
  pub name: String,
  pub args: Vec<String>,
}

pub(crate) fn tokenize_name<'t>(input: &'t [u8]) -> Vec<&'t [u8]> {
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

        tokens.push(&input[start..i]);
      },
      Some(b'(' | b')' | b',') => {
        tokens.push(&input[i..(i + 1)]);
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
              tokens.push(&input[start..i]);
              break
            }
          }
        }
      },
      Some(b'.') if matches!(input.get(i..(i + 3)), Some(b"...")) => {
        tokens.push(&input[i..(i + 3)]);
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

impl MacroSig {
  pub fn parse<'i, I>(input: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputTake + InputLength + InputIter + Compare<&'static str> + FindSubstring<&'static str> + Copy,
    <I as InputIter>::Item: AsChar,
  {
    let (input, name) = identifier(input)?;

    let (input, args) = all_consuming(parenthesized(alt((
      map(token("..."), |var_arg| vec![var_arg.to_owned()]),
      map(
        tuple((
          separated_list0(tuple((meta, token(","), meta)), identifier),
          opt(tuple((tuple((meta, token(","), meta)), map(token("..."), |var_arg| var_arg.to_owned())))),
        )),
        |(arguments, var_arg)| {
          let mut arguments = arguments.to_vec();

          if let Some((_, var_arg)) = var_arg {
            arguments.push(var_arg);
          }

          arguments
        },
      ),
    ))))(input)?;

    Ok((input, MacroSig { name, args }))
  }
}
