use std::str;

use nom::branch::alt;
use nom::combinator::all_consuming;
use nom::combinator::map;
use nom::combinator::opt;
use nom::multi::separated_list0;
use nom::sequence::tuple;
use nom::IResult;

use crate::ast::identifier;
use crate::ast::{meta, parenthesized, token};

/// The signature of a macro.
#[derive(Debug)]
pub struct MacroSig<'t> {
  pub name: &'t str,
  pub args: Vec<&'t str>,
}

pub(crate) fn tokenize_name(input: &[u8]) -> Vec<&str> {
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
              break
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

    let (input, args) = all_consuming(parenthesized(alt((
      map(token("..."), |var_arg| vec![var_arg]),
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
    ))))(input)?;
    assert!(input.is_empty());

    Ok((input, MacroSig { name, args }))
  }
}
