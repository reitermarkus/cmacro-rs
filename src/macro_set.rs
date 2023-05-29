use std::{
  borrow::Cow,
  collections::{HashMap, HashSet},
  fmt,
  iter::IntoIterator,
  mem,
};

use crate::{
  ast::is_identifier,
  token::{Comment, MacroArg},
};

fn is_punctuation(s: &str) -> bool {
  matches!(
    s,
    "["
      | "]"
      | "("
      | ")"
      | "{"
      | "}"
      | "."
      | "->"
      | "++"
      | "--"
      | "&"
      | "*"
      | "+"
      | "-"
      | "~"
      | "!"
      | "/"
      | "%"
      | "<<"
      | ">>"
      | "<"
      | ">"
      | "<="
      | ">="
      | "=="
      | "!="
      | "^"
      | "|"
      | "&&"
      | "||"
      | "?"
      | ":"
      | ";"
      | "..."
      | "="
      | "*="
      | "/="
      | "%="
      | "+="
      | "-="
      | "<<="
      | ">>="
      | "&="
      | "^="
      | "|="
      | ","
      | "#"
      | "##"
      | "<:"
      | ":>"
      | "<%"
      | "%>"
      | "%:"
      | "%:%:"
  )
}

/// A set of macros.
///
/// C macros can only be fully expanded once all macros are defined.
#[derive(Debug, Clone, Default)]
pub struct MacroSet {
  var_macros: HashMap<String, Vec<String>>,
  fn_macros: HashMap<String, (Vec<String>, Vec<String>)>,
}

/// Error during macro expansion.
#[derive(Debug, PartialEq)]
pub enum ExpansionError {
  /// Macro not found.
  MacroNotFound,
  /// Open parenthesis not found.
  MissingOpenParenthesis(char),
  /// Unclosed parenthesis.
  UnclosedParenthesis(char),
  /// Function-like macro called with wrong number of arguments.
  FnMacroArgumentError {
    /// The macro name.
    name: String,
    /// The required number of arguments.
    required: usize,
    /// The given number of arguments.
    given: usize,
  },
  /// Macro starts with `##`.
  ConcatBegin,
  /// Macro ends with `##`.
  ConcatEnd,
  /// `__VA_ARGS__` used in non-variadic macro.
  NonVariadicVarArgs,
  /// Function-like macro argument is not unique.
  NonUniqueArgument(String),
  /// `#` in function-like macro is not followed by an argument.
  StringifyNonArgument,
  /// Concatenation does not produce a valid pre-processing token.
  InvalidConcat,
}

impl fmt::Display for ExpansionError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::MacroNotFound => "macro not found".fmt(f),
      Self::MissingOpenParenthesis(c) => {
        write!(f, "missing open parenthesis for {c}")
      },
      Self::UnclosedParenthesis(c) => {
        write!(f, "missing closing parenthesis for {c}")
      },
      Self::FnMacroArgumentError { name, required, given } => {
        write!(f, "macro {name} requires {required} arguments, {given} given")
      },
      Self::ConcatBegin => "macro starts with `##`".fmt(f),
      Self::ConcatEnd => "macro ends with `##`".fmt(f),
      Self::NonVariadicVarArgs => "`__VA_ARGS__` found in non-variadic macro".fmt(f),
      Self::NonUniqueArgument(arg) => write!(f, "macro argument {arg} is not unique"),
      Self::StringifyNonArgument => "`#` is not followed by a macro parameter".fmt(f),
      Self::InvalidConcat => "concatenation does not produce a valid pre-processing token".fmt(f),
    }
  }
}

fn is_comment(s: &str) -> bool {
  (s.starts_with("/*") && s.ends_with("*/")) || s.starts_with("//")
}

fn is_whitespace(s: &str) -> bool {
  let s = s.trim();
  s.is_empty() || is_comment(s)
}

fn tokenize<'t>(arg_names: &[String], tokens: &'t [String]) -> Vec<Token<'t>> {
  tokens
    .iter()
    .map(|t| {
      if let Some(arg_index) = arg_names.iter().position(|arg_name| t == arg_name) {
        Token::MacroArg(arg_index)
      } else {
        match t.as_ref() {
          "__VA_ARGS__" => Token::VarArgs,
          "__LINE__" => Token::Line,
          token if is_comment(token) => Token::Comment(token),
          token if is_punctuation(token) => Token::Punctuation(token),
          token if is_identifier(token) => Token::Identifier(Cow::Borrowed(token)),
          token => Token::Plain(Cow::Borrowed(token)),
        }
      }
    })
    .collect()
}

fn stringify(tokens: Vec<Token<'_>>, nested: bool) -> Vec<Token<'_>> {
  let it = tokens.into_iter().peekable();
  let mut tokens = vec![];

  let mut space_before_next = false;

  let mut current_string = None;

  for token in it {
    let token = match token {
      Token::MacroArg(index) => {
        tokens.extend(current_string.take().map(|s| Token::Plain(Cow::Owned(format!("{s:?}")))));
        tokens.push(Token::Punctuation("#"));
        tokens.push(Token::MacroArg(index));
        continue
      },
      Token::VarArgs => {
        if !nested {
          "__VA_ARGS__"
        } else {
          tokens.extend(current_string.take().map(|s| Token::Plain(Cow::Owned(format!("{s:?}")))));
          tokens.push(Token::Punctuation("#"));
          tokens.push(Token::VarArgs);
          continue
        }
      },
      Token::Line => {
        if !nested {
          "__LINE__"
        } else {
          tokens.extend(current_string.take().map(|s| Token::Plain(Cow::Owned(format!("{s:?}")))));
          tokens.push(Token::Punctuation("#"));
          tokens.push(Token::Line);
          continue
        }
      },
      Token::Identifier(ref t) => t.as_ref(),
      Token::Plain(ref t) => t.as_ref(),
      Token::Punctuation(t) => t,
      Token::Placemarker => continue,
      Token::Comment(_) => continue,
    };

    let s = current_string.get_or_insert(String::new());

    if token != ")" && token != "]" && token != "}" && token != "." && token != "," && token != "(" && space_before_next
    {
      s.push(' ');
    }

    space_before_next = !(token == "(" || token == "[" || token == "{" || token == ".");

    s.push_str(token)
  }

  tokens.extend(current_string.take().map(|s| Token::Plain(Cow::Owned(format!("{s:?}")))));

  if tokens.is_empty() {
    return vec![Token::Plain(Cow::Borrowed("\"\""))]
  }

  tokens
}

fn detokenize<'t>(arg_names: &'t [String], tokens: Vec<Token<'t>>) -> Vec<MacroToken<'t>> {
  tokens
    .into_iter()
    .filter_map(|t| {
      Some(match t {
        Token::MacroArg(arg_index) => MacroToken::Arg(MacroArg { index: arg_index }),
        Token::VarArgs => MacroToken::Arg(MacroArg { index: arg_names.len() - 1 }),
        Token::Line => MacroToken::Token(Cow::Borrowed("__LINE__")),
        Token::Identifier(t) | Token::Plain(t) => MacroToken::Token(t),
        Token::Punctuation(t) => MacroToken::Token(Cow::Borrowed(t)),
        Token::Comment(t) => MacroToken::Comment(Comment { comment: Cow::Borrowed(t) }),
        Token::Placemarker => return None,
      })
    })
    .collect()
}

/// A macro token.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroToken<'t> {
  /// A macro parameter for the argument at the given position.
  Arg(MacroArg),
  /// A macro token.
  Token(Cow<'t, str>),
  /// A comment.
  Comment(Comment<'t>),
}

#[derive(Debug, Clone, PartialEq)]
enum Token<'t> {
  MacroArg(usize),
  VarArgs,
  Identifier(Cow<'t, str>),
  Plain(Cow<'t, str>),
  Punctuation(&'t str),
  Comment(&'t str),
  Line,
  Placemarker,
}

impl MacroSet {
  /// Create a new macro set.
  pub fn new() -> Self {
    Self::default()
  }

  fn contains_var_args(body: &[Token<'_>]) -> bool {
    body.iter().any(|t| *t == Token::VarArgs)
  }

  fn expand_macro_body<'s>(
    &'s self,
    non_replaced_names: HashSet<&str>,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    let mut tokens = vec![];
    let mut it = body.iter().cloned().peekable();

    while let Some(token) = it.next() {
      match token {
        Token::Identifier(id) => {
          if non_replaced_names.contains(id.as_ref()) {
            tokens.push(Token::Plain(id));
          } else {
            // Treat as function-like macro call if immediately followed by `(`.
            if it.peek() == Some(&Token::Punctuation("(")) {
              if let Some((arg_names, body)) = self.fn_macros.get(id.as_ref()) {
                if let Ok(args) = self.collect_args(&mut it) {
                  let body = tokenize(arg_names, body);
                  let expanded_tokens = self.expand_fn_macro_body(
                    non_replaced_names.clone(),
                    id.as_ref(),
                    arg_names,
                    Some(&args),
                    &body,
                  )?;
                  tokens.extend(expanded_tokens);
                  tokens.extend(it);
                  return self.expand_macro_body(non_replaced_names, &tokens)
                }
              }
            }

            // If it's not a macro call, check if it is a variable-like macro.
            if let Some(body) = self.var_macros.get(id.as_ref()) {
              let body = tokenize(&[], body);
              tokens.extend(self.expand_var_macro_body(non_replaced_names.clone(), id.as_ref(), &body)?);
              tokens.extend(it);
              return self.expand_macro_body(non_replaced_names, &tokens)
            }

            tokens.push(Token::Identifier(id))
          }
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn expand_var_macro_body<'s, 'n>(
    &'s self,
    mut non_replaced_names: HashSet<&'n str>,
    name: &'n str,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    // Variable-like macros shall not contain `__VA_ARGS__`.
    if Self::contains_var_args(body) {
      return Err(ExpansionError::NonVariadicVarArgs)
    }

    let mut body = Self::expand_concat(body.to_vec())?;
    Self::remove_placemarkers(&mut body);

    non_replaced_names.insert(name);

    self.expand_macro_body(non_replaced_names, &body)
  }

  fn expand_fn_macro_body<'s, 'n>(
    &'s self,
    mut non_replaced_names: HashSet<&'n str>,
    name: &'n str,
    arg_names: &[String],
    args: Option<&[Vec<Token<'s>>]>,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    let is_variadic = arg_names.last().map(|arg_name| *arg_name == "...").unwrap_or(false);

    if !is_variadic {
      // Function-like macros shall only contain `__VA_ARGS__` if it uses ellipsis notation in the parameters.
      if Self::contains_var_args(body) {
        return Err(ExpansionError::NonVariadicVarArgs)
      }

      if let Some(args) = args {
        if arg_names.len() != args.len()
          // Allow passing an empty argument for arity 0.
          && !(arg_names.is_empty() && args.first().map(|arg| arg.is_empty()).unwrap_or(true))
        {
          return Err(ExpansionError::FnMacroArgumentError {
            name: name.to_owned(),
            required: arg_names.len(),
            given: args.len(),
          })
        }
      }
    }

    // Parameter names must be unique.
    if let Some((_, duplicate_parameter)) = arg_names
      .iter()
      .enumerate()
      .find(|(i, arg_name)| arg_names.iter().skip(i + 1).any(|arg_name2| *arg_name == arg_name2))
    {
      return Err(ExpansionError::NonUniqueArgument(duplicate_parameter.clone()))
    }

    let body = if let Some(args) = args {
      self.expand_arguments(non_replaced_names.clone(), arg_names, args, body)?
    } else {
      body.to_vec()
    };

    let mut body = Self::expand_concat(body)?;
    Self::remove_placemarkers(&mut body);

    non_replaced_names.insert(name);

    self.expand_macro_body(non_replaced_names, &body)
  }

  fn collect_args<'s, I>(&'s self, it: &mut I) -> Result<Vec<Vec<Token<'s>>>, ExpansionError>
  where
    I: Iterator<Item = Token<'s>> + Clone,
  {
    let mut parentheses = vec![]; // Keep track of parenthesis pairs.
    let mut args = vec![];
    let mut current_arg = vec![];

    let mut it2 = it.clone();

    match it2.next() {
      Some(Token::Punctuation("(")) => (),
      _ => return Err(ExpansionError::MissingOpenParenthesis('(')),
    }

    while let Some(token) = it2.next() {
      match token {
        Token::Punctuation(p) => {
          let pop = |parentheses: &mut Vec<char>, open, close| match parentheses.pop() {
            Some(p) => {
              if p == open {
                Ok(())
              } else {
                Err(ExpansionError::UnclosedParenthesis(p))
              }
            },
            None => Err(ExpansionError::MissingOpenParenthesis(close)),
          };

          match p {
            "(" => parentheses.push('('),
            ")" => {
              if parentheses.is_empty() {
                args.push(mem::take(&mut current_arg));

                *it = it2;
                return Ok(args)
              } else {
                pop(&mut parentheses, '(', ')')?
              }
            },
            "[" => parentheses.push('['),
            "]" => pop(&mut parentheses, '[', ']')?,
            "{" => parentheses.push('{'),
            "}" => pop(&mut parentheses, '{', '}')?,
            "," => {
              if parentheses.is_empty() {
                args.push(mem::take(&mut current_arg));
                continue
              }
            },
            _ => (),
          }

          current_arg.push(Token::Punctuation(p));
        },
        token => current_arg.push(token),
      }
    }

    Err(ExpansionError::UnclosedParenthesis('('))
  }

  fn expand_arguments<'s>(
    &'s self,
    non_replaced_names: HashSet<&str>,
    arg_names: &[String],
    args: &[Vec<Token<'s>>],
    tokens: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    let mut it = tokens.iter().cloned().peekable();
    let mut tokens = vec![];

    while let Some(token) = it.next() {
      match token {
        Token::Punctuation("#") => match it.peek() {
          Some(Token::MacroArg(_) | Token::VarArgs) => {
            tokens.push(token.clone());
          },
          _ => return Err(ExpansionError::StringifyNonArgument),
        },
        Token::MacroArg(_) | Token::VarArgs => {
          let arg = if let Token::MacroArg(arg_index) = token {
            args[arg_index].clone()
          } else {
            let mut var_args = vec![];

            for (i, arg) in args[(arg_names.len() - 1)..].iter().enumerate() {
              if i > 0 {
                var_args.push(Token::Punctuation(","));
              }
              var_args.extend(arg.clone());
            }

            var_args
          };

          match tokens.last() {
            Some(Token::Punctuation("#")) => {
              tokens.pop();
              tokens.extend(stringify(arg, non_replaced_names.len() > 1));
            },
            Some(Token::Punctuation("##")) => {
              let arg = self.expand_macro_body(non_replaced_names.clone(), &arg)?;

              if arg.is_empty() {
                tokens.push(Token::Placemarker);
              } else {
                tokens.extend(arg);
              }
            },
            _ if it.peek() == Some(&Token::Punctuation("##")) => {
              let arg = self.expand_macro_body(non_replaced_names.clone(), &arg)?;

              if arg.is_empty() {
                tokens.push(Token::Placemarker);
              } else {
                tokens.extend(arg);
              }
            },
            _ => tokens.extend(self.expand_macro_body(non_replaced_names.clone(), &arg)?),
          }
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn expand_concat(tokens: Vec<Token<'_>>) -> Result<Vec<Token<'_>>, ExpansionError> {
    let mut it = tokens.into_iter().peekable();
    let mut tokens = vec![];

    while let Some(token) = it.next() {
      match token {
        Token::Punctuation("##")
          if !matches!(tokens.last(), Some(&Token::MacroArg(_) | &Token::VarArgs | &Token::Line))
            && !matches!(it.peek(), Some(&Token::MacroArg(_) | &Token::VarArgs | &Token::Line)) =>
        {
          macro_rules! until_no_whitespace {
            ($expr:expr, $error:ident) => {{
              loop {
                match $expr {
                  Some(Token::Comment(_)) => continue,
                  Some(token) => break token,
                  // Macros may not start or and with `##`.
                  None => return Err(ExpansionError::$error),
                }
              }
            }};
          }

          // Ignore whitespace between the last non-whitespace token and this `##`.
          let lhs = until_no_whitespace!(tokens.pop(), ConcatBegin);
          let rhs = if it.peek() == Some(&Token::Punctuation("##")) {
            // Treat consecutive `##` as one.
            Token::Placemarker
          } else {
            // Ignore whitespace between this `##` and the next non-whitespace token.
            until_no_whitespace!(it.next(), ConcatEnd)
          };
          tokens.push(match (lhs, rhs) {
            (Token::Placemarker, rhs) => rhs,
            (lhs, Token::Placemarker) => lhs,
            (Token::Punctuation(lhs), Token::Punctuation(rhs)) => {
              let mut token = Cow::Borrowed(lhs);
              token.to_mut().push_str(rhs.as_ref());
              Token::Plain(token)
            },
            (Token::Punctuation(lhs), Token::Identifier(rhs) | Token::Plain(rhs)) => {
              let mut token = Cow::Borrowed(lhs);
              token.to_mut().push_str(rhs.as_ref());
              Token::Plain(token)
            },
            (Token::Identifier(lhs) | Token::Plain(lhs), Token::Punctuation(rhs)) => {
              let mut token = lhs;
              token.to_mut().push_str(rhs.as_ref());
              Token::Plain(token)
            },
            (Token::Identifier(lhs), Token::Identifier(rhs)) => {
              let mut id = lhs;
              id.to_mut().push_str(rhs.as_ref());
              Token::Identifier(id)
            },
            (Token::Identifier(lhs) | Token::Plain(lhs), Token::Identifier(rhs) | Token::Plain(rhs)) => {
              let lhs_is_string_or_char_prefix = match lhs.as_ref() {
                "u8" => true,
                "u" => true,
                "U" => true,
                "L" => true,
                lhs => {
                  // Cannot concatenate anything with a string or character literal.
                  if lhs.ends_with('\"') || lhs.ends_with('\'') {
                    return Err(ExpansionError::InvalidConcat)
                  } else {
                    false
                  }
                },
              };

              if rhs.ends_with('\"') || rhs.ends_with('\'') {
                let rhs_is_unprefixed_string_or_char = rhs.starts_with('\"') || rhs.starts_with('\'');

                // Can only concatenate a string or character literal with a
                // string or character prefix if it isn't already prefixed.
                if lhs_is_string_or_char_prefix && rhs_is_unprefixed_string_or_char {
                  Token::Plain(Cow::Owned(format!("{lhs}{rhs}")))
                } else {
                  return Err(ExpansionError::InvalidConcat)
                }
              } else {
                let mut token = lhs;
                token.to_mut().push_str(rhs.as_ref());

                if is_identifier(token.as_ref()) {
                  Token::Identifier(token)
                } else {
                  Token::Plain(token)
                }
              }
            },
            (Token::MacroArg(_) | Token::VarArgs | Token::Line | Token::Comment(_), _)
            | (_, Token::MacroArg(_) | Token::VarArgs | Token::Line | Token::Comment(_)) => unreachable!(),
          })
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn remove_placemarkers(tokens: &mut Vec<Token<'_>>) {
    tokens.retain(|t| *t != Token::Placemarker);
  }

  /// Define a variable-like macro.
  ///
  /// Returns true if the macro was redefined.
  pub fn define_var_macro<N, B>(&mut self, name: N, body: B) -> bool
  where
    N: Into<String>,
    B: IntoIterator,
    B::Item: Into<String>,
  {
    let name = name.into();
    let body = body.into_iter().map(|t| t.into()).collect::<Vec<_>>();

    let redefined = if let Some(old_body) = self.var_macros.remove(&name) {
      let old_tokens = old_body.iter().filter(|t| !is_whitespace(t));
      let new_tokens = body.iter().filter(|t| !is_whitespace(t));

      !old_tokens.zip(new_tokens).all(|(t1, t2)| t1 == t2)
    } else {
      self.fn_macros.remove(&name).is_some()
    };

    self.var_macros.insert(name, body);

    redefined
  }

  /// Define a function-like macro.
  ///
  /// Returns true if the macro was redefined.
  pub fn define_fn_macro<N, A, B>(&mut self, name: N, args: A, body: B) -> bool
  where
    N: Into<String>,
    A: IntoIterator,
    A::Item: Into<String>,
    B: IntoIterator,
    B::Item: Into<String>,
  {
    let name = name.into();
    let args = args.into_iter().map(|a| a.into()).collect::<Vec<_>>();
    let body = body.into_iter().map(|a| a.into()).collect::<Vec<_>>();

    let redefined = if let Some((old_args, old_body)) = self.fn_macros.remove(&name) {
      let old_args = old_args.iter().filter(|t| !is_whitespace(t));
      let new_args = args.iter().filter(|t| !is_whitespace(t));
      let args_equal = old_args.zip(new_args).all(|(old_arg, arg)| old_arg == arg);

      let old_tokens = old_body.iter().filter(|t| !is_whitespace(t));
      let new_tokens = body.iter().filter(|t| !is_whitespace(t));
      let tokens_equal = old_tokens.zip(new_tokens).all(|(t1, t2)| t1 == t2);

      !(args_equal && tokens_equal)
    } else {
      self.var_macros.remove(&name).is_some()
    };

    self.fn_macros.insert(name, (args, body));

    redefined
  }

  /// Undefine a macro with the given name.
  ///
  /// Returns true if the macro was undefined.
  pub fn undefine_macro(&mut self, name: &str) -> bool {
    self.var_macros.remove(name).is_some() || self.fn_macros.remove(name).is_some()
  }

  /// Expand a variable-like macro.
  pub fn expand_var_macro<'t>(&'t self, name: &str) -> Result<Vec<MacroToken<'t>>, ExpansionError> {
    let body = self.var_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;
    let body = tokenize(&[], body);
    let tokens = self.expand_var_macro_body(HashSet::new(), name, &body)?;
    Ok(detokenize(&[], tokens))
  }

  /// Expand a function-like macro.
  pub fn expand_fn_macro<'t>(
    &'t self,
    name: &str,
  ) -> Result<(Vec<MacroToken<'t>>, Vec<MacroToken<'t>>), ExpansionError> {
    let (arg_names, body) = self.fn_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;
    let body = tokenize(arg_names, body);
    let tokens = self.expand_fn_macro_body(HashSet::new(), name, arg_names, None, &body)?;
    Ok((
      arg_names.iter().map(|arg_name| MacroToken::Token(Cow::Borrowed(arg_name.as_ref()))).collect(),
      detokenize(arg_names, tokens),
    ))
  }
}

#[cfg(test)]
pub(crate) trait ToMacroToken<'t> {
  fn to_macro_token(self) -> MacroToken<'t>;
}

#[cfg(test)]
impl<'t> ToMacroToken<'t> for MacroToken<'t> {
  fn to_macro_token(self) -> MacroToken<'t> {
    self
  }
}

#[cfg(test)]
impl<'t> ToMacroToken<'t> for &'t str {
  fn to_macro_token(self) -> MacroToken<'t> {
    MacroToken::Token(Cow::Borrowed(self))
  }
}

#[cfg(test)]
macro_rules! arg {
  ($index:expr) => {{
    MacroToken::Arg($crate::token::MacroArg { index: $index })
  }};
}
#[cfg(test)]
pub(crate) use arg;

#[cfg(test)]
macro_rules! tokens {
  ($($token:expr),*) => {{
    #[allow(unused)]
    use $crate::macro_set::ToMacroToken;

    &[
      $(
        $token.to_macro_token()
      ),*
    ]
  }};
}
#[cfg(test)]
pub(crate) use tokens;

#[cfg(test)]
macro_rules! token_vec {
  ($($token:expr),*) => {{
    #[allow(unused)]
    use $crate::macro_set::ToMacroToken;

    vec![
      $(
        $token.to_macro_token()
      ),*
    ]
  }};
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn macro_set() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("VAR", ["A", "+", "B"]);
    macro_set.define_var_macro("A", ["2"]);
    macro_set.define_var_macro("B", ["3"]);
    macro_set.define_fn_macro("PLUS", ["A", "B"], ["A", "+", "B"]);
    macro_set.define_fn_macro("F1", ["A", "B"], ["A", "+", "VAR", "+", "B"]);
    macro_set.define_var_macro("PLUS_VAR", ["PLUS", "(", "7", ",", "8", ")"]);
    macro_set.define_var_macro("PLUS_PLUS_VAR", ["PLUS", "(", "PLUS", "(", "3", ",", "1", ")", ",", "8", ")"]);
    macro_set.define_var_macro("PLUS_VAR_VAR", ["PLUS", "(", "7", ",", "VAR", ")"]);

    assert_eq!(macro_set.expand_var_macro("VAR"), Ok(token_vec!["2", "+", "3"]));
    assert_eq!(
      macro_set.expand_fn_macro("F1"),
      Ok((token_vec!["A", "B"], token_vec![arg!(0), "+", "2", "+", "3", "+", arg!(1)]))
    );
    assert_eq!(macro_set.expand_var_macro("PLUS_VAR"), Ok(token_vec!["7", "+", "8"]));
    assert_eq!(macro_set.expand_var_macro("PLUS_PLUS_VAR"), Ok(token_vec!["3", "+", "1", "+", "8"]));
    assert_eq!(macro_set.expand_var_macro("PLUS_VAR_VAR"), Ok(token_vec!["7", "+", "2", "+", "3"]));
  }

  #[test]
  fn concat_begin_end() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT_BEGIN", ["##", "b"]);
    macro_set.define_var_macro("CONCAT_END", ["a", "##"]);
    macro_set.define_var_macro("CONCAT_BEGIN_END", ["##"]);
    macro_set.define_var_macro("CONCAT_COMMENT_BEGIN", ["/* a */", "##", "b"]);
    macro_set.define_var_macro("CONCAT_COMMENT_END", ["a", "##", "/* b */"]);
    macro_set.define_var_macro("CONCAT_COMMENT_BEGIN_END", ["/* a */", "##", "/* b */"]);

    assert_eq!(macro_set.expand_var_macro("CONCAT_BEGIN"), Err(ExpansionError::ConcatBegin));
    assert_eq!(macro_set.expand_var_macro("CONCAT_END"), Err(ExpansionError::ConcatEnd));
    assert_eq!(macro_set.expand_var_macro("CONCAT_BEGIN_END"), Err(ExpansionError::ConcatBegin));

    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_BEGIN"), Err(ExpansionError::ConcatBegin));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_END"), Err(ExpansionError::ConcatEnd));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_BEGIN_END"), Err(ExpansionError::ConcatBegin));
  }

  #[test]
  fn parse_disjunct() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("THREE_PLUS", ["3", "+"]);
    macro_set.define_var_macro("FOUR", ["4"]);
    macro_set.define_var_macro("THREE_PLUS_FOUR", ["THREE_PLUS", "FOUR"]);

    assert_eq!(macro_set.expand_var_macro("THREE_PLUS_FOUR"), Ok(token_vec!["3", "+", "4"]));
  }

  #[test]
  fn parse_fn_no_args() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC", [] as [String; 0], ["123"]);
    macro_set.define_var_macro("ONE_TWO_THREE", ["FUNC", "(", ")"]);
    assert_eq!(macro_set.expand_var_macro("ONE_TWO_THREE"), Ok(token_vec!["123"]));
  }

  #[test]
  fn parse_disjunct_fn() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC1", ["a", "b"], ["a", "+", "b"]);
    macro_set.define_var_macro("FUNC1_PARTIAL", ["FUNC1", "(", "1", ","]);
    macro_set.define_fn_macro("FUNC2", [] as [String; 0], ["FUNC1_PARTIAL", "2", ")"]);

    assert_eq!(macro_set.expand_fn_macro("FUNC2"), Ok((token_vec![], token_vec!["1", "+", "2"])));
  }

  #[test]
  fn parse_disjunct_fn_call() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("BAR", ["a", "b"], ["a", "+", "b"]);
    macro_set.define_fn_macro("FOO", [] as [String; 0], ["BAR"]);
    macro_set.define_var_macro("APLUSB", ["FOO", "(", ")", "(", "3", ",", "1", ")"]);

    assert_eq!(macro_set.expand_var_macro("APLUSB"), Ok(token_vec!["3", "+", "1"]));
  }

  #[test]
  fn parse_recursive() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC1", ["arg"], ["FUNC2", "(", "arg", ")"]);
    macro_set.define_fn_macro("FUNC2", ["arg"], ["FUNC1", "(", "arg", ")"]);
    macro_set.define_var_macro("VAR1", ["1", "+", "VAR1"]);
    assert_eq!(macro_set.expand_fn_macro("FUNC1"), Ok((token_vec!["arg"], token_vec!["FUNC1", "(", arg!(0), ")"])));
    assert_eq!(macro_set.expand_fn_macro("FUNC2"), Ok((token_vec!["arg"], token_vec!["FUNC2", "(", arg!(0), ")"])));
    assert_eq!(macro_set.expand_var_macro("VAR1"), Ok(token_vec!["1", "+", "VAR1"]));
  }

  #[test]
  fn parse_stringify() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("s", ["377"]);
    macro_set.define_fn_macro("STRINGIFY", ["s"], ["#", "s"]);
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY"), Ok((token_vec!["s"], token_vec!["#", arg!(0)])));
  }

  #[test]
  fn parse_stringify_nested() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY", ["s"], ["#", "s"]);
    macro_set.define_var_macro("s", ["STRINGIFY", "(", "asdf", ")"]);
    macro_set.define_var_macro("e", ["STRINGIFY", "(", "a", "+", "b", ")"]);
    assert_eq!(macro_set.expand_var_macro("s"), Ok(token_vec!["\"asdf\""]));
    assert_eq!(macro_set.expand_var_macro("e"), Ok(token_vec!["\"a + b\""]));
  }

  #[test]
  fn parse_stringify_double_nested() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY1", ["s"], ["#", "s"]);
    macro_set.define_fn_macro("STRINGIFY2", ["s"], ["STRINGIFY1", "(", "s", ")"]);
    macro_set.define_var_macro("LINE_STRING1", ["STRINGIFY1", "(", "__LINE__", ")"]);
    macro_set.define_var_macro("LINE_STRING2", ["STRINGIFY2", "(", "__LINE__", ")"]);
    eprintln!("STRINGIFY1");
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY1"), Ok((token_vec!["s"], token_vec!["#", arg!(0)])));
    eprintln!("STRINGIFY2");
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY2"), Ok((token_vec!["s"], token_vec!["#", arg!(0)])));
    eprintln!("LINE_STRING1");
    assert_eq!(macro_set.expand_var_macro("LINE_STRING1"), Ok(token_vec!["\"__LINE__\""]));
    eprintln!("LINE_STRING2");
    assert_eq!(macro_set.expand_var_macro("LINE_STRING2"), Ok(token_vec!["#", "__LINE__"]));
  }

  #[test]
  fn parse_stringify_var_args() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY", ["..."], ["#", "__VA_ARGS__"]);
    macro_set.define_var_macro("ZERO", ["STRINGIFY", "(", ")"]);
    macro_set.define_var_macro("ONE", ["STRINGIFY", "(", "asdf", ")"]);
    macro_set.define_var_macro("TWO", ["STRINGIFY", "(", "a", ",", "b", ")"]);
    assert_eq!(macro_set.expand_var_macro("ZERO"), Ok(token_vec!["\"\""]));
    assert_eq!(macro_set.expand_var_macro("ONE"), Ok(token_vec!["\"asdf\""]));
    assert_eq!(macro_set.expand_var_macro("TWO"), Ok(token_vec!["\"a, b\""]));
  }

  #[test]
  fn parse_wrong_arity() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("func", ["x"], ["func", "(", "x", ",", "3", ")"]);
    macro_set.define_fn_macro("wrapper_func", ["x"], ["func", "(", "x", ",", "3", ")"]);

    assert_eq!(
      macro_set.expand_fn_macro("wrapper_func"),
      Err(ExpansionError::FnMacroArgumentError { name: "func".into(), required: 1, given: 2 })
    );
  }

  #[test]
  fn parse_concat() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["1"]);
    macro_set.define_var_macro("B", ["2"]);
    macro_set.define_var_macro("CONCAT", ["A", "##", "B"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec!["AB"]));
  }

  #[test]
  fn parse_concat_comment() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT_COMMENT1", ["A", "/* 1 */", "##", "B"]);
    macro_set.define_var_macro("CONCAT_COMMENT2", ["A", "##", "/* 2 */", "B"]);
    macro_set.define_var_macro("CONCAT_COMMENT3", ["A", "/* 1 */", "##", "/* 2 */", "B"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT1"), Ok(token_vec!["AB"]));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT2"), Ok(token_vec!["AB"]));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT3"), Ok(token_vec!["AB"]));
  }

  #[test]
  fn parse_concat_string() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["1"]);
    macro_set.define_var_macro("B", ["2"]);
    macro_set.define_var_macro("C", ["\", world!\""]);
    macro_set.define_var_macro("AB", ["\"Hello\""]);
    macro_set.define_fn_macro("CONCAT_STRING", ["A", "B"], ["A", "##", "B", "C"]);
    assert_eq!(
      macro_set.expand_fn_macro("CONCAT_STRING"),
      Ok((token_vec!["A", "B"], token_vec![arg!(0), "##", arg!(1), "\", world!\""]))
    );
  }

  #[test]
  fn parse_concat_string_prefix() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["u8", "##", "\"abc\""]);
    macro_set.define_var_macro("B", ["u8", "\"abc\""]);
    macro_set.define_fn_macro("PREFIX", ["prefix"], ["prefix", "##", "\"abc\""]);
    macro_set.define_var_macro("C", ["PREFIX", "(", "u8", ")"]);
    macro_set.define_fn_macro("PREFIX_STRINGIFY", ["prefix"], ["prefix", "##", "#", "prefix"]);
    macro_set.define_var_macro("D", ["PREFIX_STRINGIFY", "(", "u8", ")"]);
    macro_set.define_fn_macro("PREFIX_HASH", ["prefix"], ["prefix", "##", "#"]);
    macro_set.define_var_macro("E", ["PREFIX_HASH", "(", "u8", ")"]);
    assert_eq!(macro_set.expand_var_macro("A"), Ok(token_vec!["u8\"abc\""]));
    assert_eq!(macro_set.expand_var_macro("B"), Ok(token_vec!["u8", "\"abc\""]));
    assert_eq!(macro_set.expand_var_macro("C"), Ok(token_vec!["u8\"abc\""]));
    assert_eq!(macro_set.expand_var_macro("D"), Ok(token_vec!["u8\"u8\""]));
    assert_eq!(macro_set.expand_var_macro("E"), Err(ExpansionError::StringifyNonArgument));
  }

  #[test]
  fn parse_concat_empty() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("CONCAT", ["a", "b"], ["a", "##", "b"]);
    macro_set.define_var_macro("EMPTY", ["CONCAT", "(", ",", ")"]);
    assert_eq!(macro_set.expand_var_macro("EMPTY"), Ok(token_vec![]));
  }

  #[test]
  fn parse_c_std_6_10_3_3_example() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("hash_hash", ["#", "##", "#"]);
    macro_set.define_fn_macro("mkstr", ["a"], ["#", "a"]);
    macro_set.define_fn_macro("in_between", ["a"], ["mkstr", "(", "a", ")"]);
    macro_set.define_fn_macro("join", ["c", "d"], ["in_between", "(", "c", "hash_hash", "d", ")"]);
    macro_set.define_var_macro("join_x_y", ["join", "(", "x", ",", "y", ")"]);
    assert_eq!(macro_set.expand_var_macro("join_x_y"), Ok(token_vec!["\"x ## y\""]));
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_3() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("x", ["3"]);
    macro_set.define_fn_macro("f", ["a"], ["f", "(", "x", "*", "(", "a", ")", ")"]);
    macro_set.define_var_macro("x", ["2"]);
    macro_set.define_var_macro("g", ["f"]);
    macro_set.define_var_macro("z", ["z", "[", "0", "]"]);
    macro_set.define_var_macro("h", ["g", "(", "~"]);
    macro_set.define_fn_macro("m", ["a"], ["a", "(", "w", ")"]);
    macro_set.define_var_macro("w", ["0", ",", "1"]);
    macro_set.define_fn_macro("t", ["a"], ["a"]);
    macro_set.define_fn_macro("p", [] as [String; 0], ["int"]);
    macro_set.define_fn_macro("q", ["x"], ["x"]);
    macro_set.define_fn_macro("r", ["x", "y"], ["x", "##", "y"]);
    macro_set.define_fn_macro("str", ["x"], ["#", "x"]);

    macro_set.define_var_macro(
      "line1",
      [
        "f", "(", "y", "+", "1", ")", "+", "f", "(", "f", "(", "z", ")", ")", "%", "t", "(", "t", "(", "g", ")", "(",
        "0", ")", "+", "t", ")", "(", "1", ")", ";",
      ],
    );
    macro_set.define_var_macro(
      "line2",
      [
        "g", "(", "x", "+", "(", "3", ",", "4", ")", "-", "w", ")", "|", "h", "5", ")", "&", "m", "(", "f", ")", "^",
        "m", "(", "m", ")", ";",
      ],
    );
    macro_set.define_var_macro(
      "line3",
      [
        "p", "(", ")", "i", "[", "q", "(", ")", "]", "=", "{", "q", "(", "1", ")", ",", "r", "(", "2", ",", "3", ")",
        ",", "r", "(", "4", ",", ")", ",", "r", "(", ",", "5", ")", ",", "r", "(", ",", ")", "}", ";",
      ],
    );
    macro_set.define_var_macro(
      "line4",
      ["char", "c", "[", "2", "]", "[", "6", "]", "=", "{", "str", "(", "hello", ")", ",", "str", "(", ")", "}", ";"],
    );

    assert_eq!(
      macro_set.expand_var_macro("line1"),
      Ok(token_vec![
        "f", "(", "2", "*", "(", "y", "+", "1", ")", ")", "+", "f", "(", "2", "*", "(", "f", "(", "2", "*", "(", "z",
        "[", "0", "]", ")", ")", ")", ")", "%", "f", "(", "2", "*", "(", "0", ")", ")", "+", "t", "(", "1", ")", ";"
      ])
    );
    assert_eq!(
      macro_set.expand_var_macro("line2"),
      Ok(token_vec![
        "f", "(", "2", "*", "(", "2", "+", "(", "3", ",", "4", ")", "-", "0", ",", "1", ")", ")", "|", "f", "(", "2",
        "*", "(", "~", "5", ")", ")", "&", "f", "(", "2", "*", "(", "0", ",", "1", ")", ")", "^", "m", "(", "0", ",",
        "1", ")", ";"
      ])
    );
    assert_eq!(
      macro_set.expand_var_macro("line3"),
      Ok(token_vec!["int", "i", "[", "]", "=", "{", "1", ",", "23", ",", "4", ",", "5", ",", "}", ";"])
    );
    assert_eq!(
      macro_set.expand_var_macro("line4"),
      Ok(token_vec!["char", "c", "[", "2", "]", "[", "6", "]", "=", "{", "\"hello\"", ",", "\"\"", "}", ";"])
    );
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_4() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("str", ["s"], ["#", "s"]);
    macro_set.define_fn_macro("xstr", ["s"], ["str", "(", "s", ")"]);
    macro_set.define_fn_macro(
      "debug",
      ["s", "t"],
      [
        "printf",
        "(",
        "\"x\"",
        "#",
        "s",
        "\"= %d, x\"",
        "#",
        "t",
        "\"= %s\"",
        ",",
        "x",
        "##",
        "s",
        ",",
        "x",
        "##",
        "t",
        ")",
      ],
    );
    macro_set.define_fn_macro("INCFILE", ["n"], ["vers", "##", "n"]);
    macro_set.define_fn_macro("glue", ["a", "b"], ["a", "##", "b"]);
    macro_set.define_fn_macro("xglue", ["a", "b"], ["glue", "(", "a", ",", "b", ")"]);
    macro_set.define_var_macro("HIGHLOW", ["\"hello\""]);
    macro_set.define_var_macro("LOW", ["LOW", "\", world\""]);

    macro_set.define_var_macro("line1", ["debug", "(", "1", ",", "2", ")", ";"]);
    macro_set.define_var_macro(
      "line2",
      [
        "fputs",
        "(",
        "str",
        "(",
        "strncmp",
        "(",
        "\"abc\\0d\"",
        ",",
        "\"abc\"",
        ",",
        "'\\4'",
        ")", // this goes away
        "==",
        "0",
        ")",
        "str",
        "(",
        ":",
        "@",
        "\\n",
        ")",
        ",",
        "s",
        ")",
        ";",
      ],
    );
    macro_set.define_var_macro("line3", ["#include", "xstr", "(", "INCFILE", "(", "2", ")", ".", "h", ")"]);

    assert_eq!(
      macro_set.expand_var_macro("line1"),
      Ok(token_vec![
        "printf",
        "(",
        "\"x\"",
        "\"1\"",
        "\"= %d, x\"",
        "\"2\"",
        "\"= %s\"",
        ",",
        "x1",
        ",",
        "x2",
        ")",
        ";"
      ])
    );
    assert_eq!(
      macro_set.expand_var_macro("line2"),
      Ok(token_vec![
        "fputs",
        "(",
        "\"strncmp(\\\"abc\\\\0d\\\", \\\"abc\\\", '\\\\4') == 0\"",
        "\": @ \\\\n\"",
        ",",
        "s",
        ")",
        ";"
      ])
    );
    assert_eq!(macro_set.expand_var_macro("line3"), Ok(token_vec!["#include", "\"vers2.h\""]));
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_5() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("t", ["x", "y", "z"], ["x", "##", "y", "##", "z"]);
    macro_set.define_var_macro(
      "line1",
      [
        "int", "j", "[", "]", "=", "{", //
        "t", "(", "1", ",", "2", ",", "3", ")", ",", //
        "t", "(", ",", "4", ",", "5", ")", ",", //
        "t", "(", "6", ",", ",", "7", ")", ",", //
        "t", "(", "8", ",", "9", ",", ")", ",", //
        "t", "(", "10", ",", ",", ")", ",", //
        "t", "(", ",", "11", ",", ")", ",", //
        "t", "(", ",", ",", "12", ")", ",", //
        "t", "(", ",", ",", ")", //
        "}", ";",
      ],
    );

    assert_eq!(
      macro_set.expand_var_macro("line1"),
      Ok(token_vec![
        "int", "j", "[", "]", "=", "{", "123", ",", "45", ",", "67", ",", "89", ",", "10", ",", "11", ",", "12", ",",
        "}", ";"
      ])
    );
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_6() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("OBJ_LIKE", ["/* whie space */", "(", "1", "-", "1", ")", "/* other */"]);
    assert!(!macro_set.define_var_macro("OBJ_LIKE", ["(", "1", "-", "1", ")"]));

    assert!(!macro_set.define_fn_macro("FUNC_LIKE", ["a"], ["(", "a", ")"]));
    assert!(!macro_set.define_fn_macro(
      "FUNC_LIKE",
      ["a"],
      ["(", "/* note the white space */", "a", "/* other stuff on this line \n */", ")"]
    ));

    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("OBJ_LIKE", ["(", "0", ")"]);
    assert!(macro_set.define_var_macro("OBJ_LIKE", ["(", "1", "-", "1", ")"]));

    macro_set.define_fn_macro("FUNC_LIKE", ["b"], ["(", "a", ")"]);
    assert!(macro_set.define_fn_macro("FUNC_LIKE", ["b"], ["(", "b", ")"]));
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_7() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("debug", ["..."], ["fprintf", "(", "stderr", ",", "__VA_ARGS__", ")"]);
    macro_set.define_fn_macro("showlist", ["..."], ["puts", "(", "#", "__VA_ARGS__", ")"]);
    macro_set.define_fn_macro(
      "report",
      ["test", "..."],
      ["(", "(", "test", ")", "?", "puts", "(", "#", "test", ")", ":", "printf", "(", "__VA_ARGS__", ")", ")"],
    );

    macro_set.define_var_macro("line1", ["debug", "(", "\"Flag\"", ")", ";"]);
    macro_set.define_var_macro("line2", ["debug", "(", "\"X = %d\\n\"", ",", "x", ")", ";"]);
    macro_set.define_var_macro(
      "line3",
      ["showlist", "(", "The", "first", ",", "second", ",", "and", "third", "items", ".", ")", ";"],
    );
    macro_set.define_var_macro(
      "line4",
      ["report", "(", "x", ">", "y", ",", "\"x is %d but y is %d\"", ",", "x", ",", "y", ")", ";"],
    );

    assert_eq!(
      macro_set.expand_var_macro("line1"),
      Ok(token_vec!["fprintf", "(", "stderr", ",", "\"Flag\"", ")", ";"])
    );
    assert_eq!(
      macro_set.expand_var_macro("line2"),
      Ok(token_vec!["fprintf", "(", "stderr", ",", "\"X = %d\\n\"", ",", "x", ")", ";"])
    );
    assert_eq!(
      macro_set.expand_var_macro("line3"),
      Ok(token_vec!["puts", "(", "\"The first, second, and third items.\"", ")", ";"])
    );
    assert_eq!(
      macro_set.expand_var_macro("line4"),
      Ok(token_vec![
        "(",
        "(",
        "x",
        ">",
        "y",
        ")",
        "?",
        "puts",
        "(",
        "\"x > y\"",
        ")",
        ":",
        "printf",
        "(",
        "\"x is %d but y is %d\"",
        ",",
        "x",
        ",",
        "y",
        ")",
        ")",
        ";"
      ])
    );
  }
}
