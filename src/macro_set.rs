use std::{
  collections::{HashMap, HashSet},
  mem,
};

/// A set of macros.
#[derive(Debug, Default)]
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
  /// Function-like macro parameter is not unique.
  NonUniqueParameter(String),
  /// `#` in function-like macro is not followed by a parameter.
  StringifyNonParameter,
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
          "#" => Token::Stringify,
          "##" => Token::Concat,
          token => Token::Plain(token),
        }
      }
    })
    .collect()
}

fn detokenize(arg_names: &[String], tokens: Vec<Token<'_>>) -> Vec<String> {
  tokens
    .into_iter()
    .filter_map(|t| {
      Some(match t {
        Token::MacroArg(arg_index) => arg_names[arg_index].clone(),
        Token::VarArgs => "__VA_ARGS__".into(),
        Token::Plain(t) => t.to_string(),
        Token::NonReplacable(t) => t.to_string(),
        Token::Stringify => "#".into(),
        Token::Concat => "##".into(),
        Token::StringifyArg(tokens) => {
          let mut s = String::new();

          for (i, token) in detokenize(arg_names, tokens).into_iter().enumerate() {
            if i > 0 && token != "," {
              s.push(' ');
            }
            s.push_str(&token)
          }

          format!("{:?}", s)
        },
        Token::ConcatArg(tokens) => detokenize(arg_names, tokens).join(""),
        Token::Placemarker => return None,
      })
    })
    .collect()
}

#[derive(Debug, Clone, PartialEq)]
enum Token<'s> {
  Plain(&'s str),
  MacroArg(usize),
  VarArgs,
  NonReplacable(&'s str),
  Stringify,
  Concat,
  StringifyArg(Vec<Token<'s>>),
  Placemarker,
  // TODO: Get rid of `ConcatArg`, since the resulting token is also available for macro replacement.
  ConcatArg(Vec<Token<'s>>),
}

impl MacroSet {
  /// Create a new macro set.
  pub fn new() -> Self {
    Self::default()
  }

  // Macros may not start or and with `##`.
  fn check_concat_begin_end(body: &[Token<'_>]) -> Result<(), ExpansionError> {
    if body.first() == Some(&Token::Concat) {
      return Err(ExpansionError::ConcatBegin)
    }

    if body.last() == Some(&Token::Concat) {
      return Err(ExpansionError::ConcatEnd)
    }

    Ok(())
  }

  fn contains_var_args(body: &[Token<'_>]) -> bool {
    body.iter().any(|t| *t == Token::VarArgs)
  }

  fn expand_macro_body<'s>(
    &'s self,
    non_replaced_names: HashSet<&'s str>,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    let mut tokens = vec![];
    let mut it = body.iter().cloned().peekable();

    while let Some(token) = it.next() {
      match token {
        Token::Stringify => {
          if !matches!(it.peek(), Some(Token::MacroArg(_) | Token::VarArgs)) {
            return Err(ExpansionError::StringifyNonParameter)
          }

          tokens.push(token.clone());
        },
        Token::Plain(t) => {
          if non_replaced_names.contains(t) {
            tokens.push(Token::NonReplacable(t));
          } else if let Some(body) = self.var_macros.get(t) {
            let body = tokenize(&[], body);
            tokens.extend(self.expand_var_macro_body(non_replaced_names.clone(), t, &body)?);
            tokens.extend(it);
            return self.expand_macro_body(non_replaced_names, &tokens)
          } else if let Some((arg_names, body)) = self.fn_macros.get(t) {
            if let Ok(args) = self.collect_args(&mut it) {
              let body = tokenize(arg_names, body);
              tokens.extend(self.expand_fn_macro_body(non_replaced_names.clone(), t, arg_names, Some(&args), &body)?);
              tokens.extend(it);
              return self.expand_macro_body(non_replaced_names, &tokens)
            } else {
              tokens.push(token);
            }
          } else {
            tokens.push(token)
          }
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn expand_var_macro_body<'s>(
    &'s self,
    mut non_replaced_names: HashSet<&'s str>,
    name: &'s str,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    Self::check_concat_begin_end(body)?;

    // Variable-like macros shall not contain `__VA_ARGS__`.
    if Self::contains_var_args(body) {
      return Err(ExpansionError::NonVariadicVarArgs)
    }

    non_replaced_names.insert(name);

    let body = Self::expand_concat(body.to_vec())?;

    self.expand_macro_body(non_replaced_names, &body)
  }

  // TODO: Add error for concatenating non-identifiers.
  fn concat_tokens<'s>(lhs: Token<'s>, rhs: Token<'s>) -> Token<'s> {
    match (lhs, rhs) {
      (Token::Placemarker, rhs) => rhs,
      (lhs, Token::Placemarker) => lhs,
      (lhs, rhs) => Token::ConcatArg(vec![lhs, rhs]),
    }
  }

  fn expand_fn_macro_body<'s>(
    &'s self,
    mut non_replaced_names: HashSet<&'s str>,
    name: &'s str,
    arg_names: &[String],
    args: Option<&[Vec<Token<'s>>]>,
    body: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    Self::check_concat_begin_end(body)?;

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
          dbg!((&arg_names, &args));

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
      return Err(ExpansionError::NonUniqueParameter(duplicate_parameter.clone()))
    }

    let body = if let Some(args) = args {
      self.expand_arguments(non_replaced_names.clone(), arg_names, args, body)?
    } else {
      body.to_vec()
    };

    let body = Self::expand_concat(body)?;

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
      Some(Token::Plain("(")) => (),
      _ => return Err(ExpansionError::MissingOpenParenthesis('(')),
    }

    while let Some(token) = it2.next() {
      match token {
        Token::Plain(t @ "(" | t @ "[" | t @ "{") => {
          parentheses.push(t.chars().next().unwrap());
          current_arg.push(token);
        },
        Token::Plain("}") => match parentheses.pop() {
          Some('{') => current_arg.push(token),
          Some(parenthesis) => return Err(ExpansionError::UnclosedParenthesis(parenthesis)),
          None => return Err(ExpansionError::MissingOpenParenthesis('{')),
        },
        Token::Plain("]") => match parentheses.pop() {
          Some('[') => current_arg.push(token),
          Some(parenthesis) => return Err(ExpansionError::UnclosedParenthesis(parenthesis)),
          None => return Err(ExpansionError::MissingOpenParenthesis('[')),
        },
        Token::Plain(")") => match parentheses.pop() {
          Some('(') => current_arg.push(token),
          Some(parenthesis) => return Err(ExpansionError::UnclosedParenthesis(parenthesis)),
          None => {
            args.push(mem::take(&mut current_arg));

            *it = it2;
            return Ok(args)
          },
        },
        Token::Plain(",") if parentheses.is_empty() => {
          args.push(mem::take(&mut current_arg));
        },
        token => current_arg.push(token),
      }
    }

    Err(ExpansionError::UnclosedParenthesis('('))
  }

  fn expand_arguments<'s>(
    &'s self,
    non_replaced_names: HashSet<&'s str>,
    arg_names: &[String],
    args: &[Vec<Token<'s>>],
    tokens: &[Token<'s>],
  ) -> Result<Vec<Token<'s>>, ExpansionError> {
    let mut it = tokens.iter().cloned().peekable();
    let mut tokens = vec![];

    while let Some(token) = it.next() {
      match token {
        Token::MacroArg(_) | Token::VarArgs => {
          let arg = if let Token::MacroArg(arg_index) = token {
            args[arg_index].clone()
          } else {
            let mut var_args = vec![];

            for (i, arg) in args[(arg_names.len() - 1)..].iter().enumerate() {
              if i > 0 {
                var_args.push(Token::Plain(","));
              }
              var_args.extend(arg.clone());
            }

            var_args
          };

          match tokens.last() {
            Some(Token::Stringify) => {
              tokens.pop();
              tokens.push(Token::StringifyArg(arg.clone()));
            },
            Some(Token::Concat) => {
              let arg = self.expand_macro_body(non_replaced_names.clone(), &arg)?;

              if arg.is_empty() {
                tokens.push(Token::Placemarker);
              } else {
                tokens.extend(arg);
              }
            },
            _ if it.peek() == Some(&Token::Concat) => {
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
        Token::Concat => {
          // NOTE: `##` cannot be at the beginning or end, so there must be a token before and after this.
          let lhs = tokens.pop().unwrap();
          let rhs = it.next().unwrap();
          tokens.push(Self::concat_tokens(lhs, rhs))
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  /// Add a variable-like macro to the set.
  ///
  /// Returns true if the macro was redefined.
  pub fn add_var_macro(&mut self, name: &str, body: &[&str]) -> bool {
    self.fn_macros.remove(name).is_some()
      || self.var_macros.insert(name.to_owned(), body.iter().map(|&t| t.to_owned()).collect()).is_some()
  }

  /// Parse a variable-like macro.
  pub fn parse_var_macro(&self, name: &str) -> Result<Vec<String>, ExpansionError> {
    let body = self.var_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;
    let body = tokenize(&[], body);
    let tokens = self.expand_var_macro_body(HashSet::new(), name, &body)?;
    Ok(detokenize(&[], tokens))
  }

  /// Add a function-like macro to the set.
  ///
  /// Returns true if the macro was redefined.
  pub fn add_fn_macro(&mut self, name: &str, args: &[&str], body: &[&str]) -> bool {
    self.var_macros.remove(name).is_some()
      || self
        .fn_macros
        .insert(
          name.to_owned(),
          (args.iter().map(|&t| t.to_owned()).collect(), body.iter().map(|&t| t.to_owned()).collect()),
        )
        .is_some()
  }

  /// Parse a function-like macro.
  pub fn parse_fn_macro(&self, name: &str) -> Result<Vec<String>, ExpansionError> {
    let (arg_names, body) = self.fn_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;
    let body = tokenize(arg_names, body);
    let tokens = self.expand_fn_macro_body(HashSet::new(), name, arg_names, None, &body)?;
    Ok(detokenize(arg_names, tokens))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! tokens {
    ($($token:expr),*) => {{
      vec![
        $(
          String::from($token)
        ),*
      ]
    }};
  }

  #[test]
  fn macro_set() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("VAR", &["A", "+", "B"]);
    macro_set.add_var_macro("A", &["2"]);
    macro_set.add_var_macro("B", &["3"]);
    macro_set.add_fn_macro("PLUS", &["A", "B"], &["A", "+", "B"]);
    macro_set.add_fn_macro("F1", &["A", "B"], &["A", "+", "VAR", "+", "B"]);
    macro_set.add_var_macro("PLUS_VAR", &["PLUS", "(", "7", ",", "8", ")"]);
    macro_set.add_var_macro("PLUS_PLUS_VAR", &["PLUS", "(", "PLUS", "(", "3", ",", "1", ")", ",", "8", ")"]);
    macro_set.add_var_macro("PLUS_VAR_VAR", &["PLUS", "(", "7", ",", "VAR", ")"]);

    assert_eq!(macro_set.parse_var_macro("VAR"), Ok(tokens!["2", "+", "3"]));
    assert_eq!(macro_set.parse_fn_macro("F1"), Ok(tokens!["A", "+", "2", "+", "3", "+", "B"]));
    assert_eq!(macro_set.parse_var_macro("PLUS_VAR"), Ok(tokens!["7", "+", "8"]));
    assert_eq!(macro_set.parse_var_macro("PLUS_PLUS_VAR"), Ok(tokens!["3", "+", "1", "+", "8"]));
    assert_eq!(macro_set.parse_var_macro("PLUS_VAR_VAR"), Ok(tokens!["7", "+", "2", "+", "3"]));
  }

  #[test]
  fn parse_disjunct() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("THREE_PLUS", &["3", "+"]);
    macro_set.add_var_macro("FOUR", &["4"]);
    macro_set.add_var_macro("THREE_PLUS_FOUR", &["THREE_PLUS", "FOUR"]);

    assert_eq!(macro_set.parse_var_macro("THREE_PLUS_FOUR"), Ok(tokens!["3", "+", "4"]));
  }

  #[test]
  fn parse_fn_no_args() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("FUNC", &[], &["123"]);
    macro_set.add_var_macro("ONE_TWO_THREE", &["FUNC", "(", ")"]);
    assert_eq!(macro_set.parse_var_macro("ONE_TWO_THREE"), Ok(tokens!["123"]));
  }

  #[test]
  fn parse_disjunct_fn() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("FUNC1", &["a", "b"], &["a", "+", "b"]);
    macro_set.add_var_macro("FUNC1_PARTIAL", &["FUNC1", "(", "1", ","]);
    macro_set.add_fn_macro("FUNC2", &[], &["FUNC1_PARTIAL", "2", ")"]);

    assert_eq!(macro_set.parse_fn_macro("FUNC2"), Ok(tokens!["1", "+", "2"]));
  }

  #[test]
  fn parse_disjunct_fn_call() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("BAR", &["a", "b"], &["a", "+", "b"]);
    macro_set.add_fn_macro("FOO", &[], &["BAR"]);
    macro_set.add_var_macro("APLUSB", &["FOO", "(", ")", "(", "3", ",", "1", ")"]);

    assert_eq!(macro_set.parse_var_macro("APLUSB"), Ok(tokens!["3", "+", "1"]));
  }

  #[test]
  fn parse_recursive() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("FUNC1", &["arg"], &["FUNC2", "(", "arg", ")"]);
    macro_set.add_fn_macro("FUNC2", &["arg"], &["FUNC1", "(", "arg", ")"]);
    macro_set.add_var_macro("VAR1", &["1", "+", "VAR1"]);
    assert_eq!(macro_set.parse_fn_macro("FUNC1"), Ok(tokens!["FUNC1", "(", "arg", ")"]));
    assert_eq!(macro_set.parse_fn_macro("FUNC2"), Ok(tokens!["FUNC2", "(", "arg", ")"]));
    assert_eq!(macro_set.parse_var_macro("VAR1"), Ok(tokens!["1", "+", "VAR1"]));
  }

  #[test]
  fn parse_stringify() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("s", &["377"]);
    macro_set.add_fn_macro("STRINGIFY", &["s"], &["#", "s"]);
    assert_eq!(macro_set.parse_fn_macro("STRINGIFY"), Ok(tokens!["#", "s"]));
  }

  #[test]
  fn parse_stringify_nested() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("STRINGIFY", &["s"], &["#", "s"]);
    macro_set.add_var_macro("s", &["STRINGIFY", "(", "asdf", ")"]);
    macro_set.add_var_macro("e", &["STRINGIFY", "(", "a", "+", "b", ")"]);
    assert_eq!(macro_set.parse_var_macro("s"), Ok(tokens!["\"asdf\""]));
    assert_eq!(macro_set.parse_var_macro("e"), Ok(tokens!["\"a + b\""]));
  }

  #[test]
  fn parse_stringify_var_args() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("STRINGIFY", &["..."], &["#", "__VA_ARGS__"]);
    macro_set.add_var_macro("ZERO", &["STRINGIFY", "(", ")"]);
    macro_set.add_var_macro("ONE", &["STRINGIFY", "(", "asdf", ")"]);
    macro_set.add_var_macro("TWO", &["STRINGIFY", "(", "a", ",", "b", ")"]);
    assert_eq!(macro_set.parse_var_macro("ZERO"), Ok(tokens!["\"\""]));
    assert_eq!(macro_set.parse_var_macro("ONE"), Ok(tokens!["\"asdf\""]));
    assert_eq!(macro_set.parse_var_macro("TWO"), Ok(tokens!["\"a, b\""]));
  }

  #[test]
  fn parse_concat() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("A", &["1"]);
    macro_set.add_var_macro("B", &["2"]);
    macro_set.add_var_macro("CONCAT", &["A", "##", "B"]);
    assert_eq!(macro_set.parse_var_macro("CONCAT"), Ok(tokens!["AB"]));
  }

  #[test]
  fn parse_concat_empty() {
    let mut macro_set = MacroSet::new();

    macro_set.add_fn_macro("CONCAT", &["a", "b"], &["a", "##", "b"]);
    macro_set.add_var_macro("EMPTY", &["CONCAT", "(", ",", ")"]);
    assert_eq!(macro_set.parse_var_macro("EMPTY"), Ok(tokens![]));
  }

  #[test]
  fn parse_c_std_6_10_3_3() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("hash_hash", &["#", "##", "#"]);
    macro_set.add_fn_macro("mkstr", &["a"], &["#", "a"]);
    macro_set.add_fn_macro("in_between", &["a"], &["mkstr", "(", "a", ")"]);
    macro_set.add_fn_macro("join", &["c", "d"], &["in_between", "(", "c", "hash_hash", "d", ")"]);
    macro_set.add_var_macro("join_x_y", &["join", "(", "x", ",", "y", ")"]);
    assert_eq!(macro_set.parse_var_macro("join_x_y"), Ok(tokens!["\"x ## y\""]));
  }

  #[test]
  fn parse_c_std_6_10_3_5() {
    let mut macro_set = MacroSet::new();

    macro_set.add_var_macro("x", &["3"]);
    macro_set.add_fn_macro("f", &["a"], &["f", "(", "x", "*", "(", "a", ")", ")"]);
    macro_set.add_var_macro("x", &["2"]);
    macro_set.add_var_macro("g", &["f"]);
    macro_set.add_var_macro("z", &["z", "[", "0", "]"]);
    macro_set.add_var_macro("h", &["g", "(", "~"]);
    macro_set.add_fn_macro("m", &["a"], &["a", "(", "w", ")"]);
    macro_set.add_var_macro("w", &["0", ",", "1"]);
    macro_set.add_fn_macro("t", &["a"], &["a"]);
    macro_set.add_fn_macro("p", &[], &["int"]);
    macro_set.add_fn_macro("q", &["x"], &["x"]);
    macro_set.add_fn_macro("r", &["x", "y"], &["x", "##", "y"]);
    macro_set.add_fn_macro("str", &["x"], &["#", "x"]);

    macro_set.add_var_macro(
      "line1",
      &[
        "f", "(", "y", "+", "1", ")", "+", "f", "(", "f", "(", "z", ")", ")", "%", "t", "(", "t", "(", "g", ")", "(",
        "0", ")", "+", "t", ")", "(", "1", ")", ";",
      ],
    );
    macro_set.add_var_macro(
      "line2",
      &[
        "g", "(", "x", "+", "(", "3", ",", "4", ")", "-", "w", ")", "|", "h", "5", ")", "&", "m", "(", "f", ")", "^",
        "m", "(", "m", ")", ";",
      ],
    );
    macro_set.add_var_macro(
      "line3",
      &[
        "p", "(", ")", "i", "[", "q", "(", ")", "]", "=", "{", "q", "(", "1", ")", ",", "r", "(", "2", ",", "3", ")",
        ",", "r", "(", "4", ",", ")", ",", "r", "(", ",", "5", ")", ",", "r", "(", ",", ")", "}", ";",
      ],
    );
    macro_set.add_var_macro(
      "line4",
      &["char", "c", "[", "2", "]", "[", "6", "]", "=", "{", "str", "(", "hello", ")", ",", "str", "(", ")", "}", ";"],
    );

    assert_eq!(
      macro_set.parse_var_macro("line1"),
      Ok(tokens![
        "f", "(", "2", "*", "(", "y", "+", "1", ")", ")", "+", "f", "(", "2", "*", "(", "f", "(", "2", "*", "(", "z",
        "[", "0", "]", ")", ")", ")", ")", "%", "f", "(", "2", "*", "(", "0", ")", ")", "+", "t", "(", "1", ")", ";"
      ])
    );
    assert_eq!(
      macro_set.parse_var_macro("line2"),
      Ok(tokens![
        "f", "(", "2", "*", "(", "2", "+", "(", "3", ",", "4", ")", "-", "0", ",", "1", ")", ")", "|", "f", "(", "2",
        "*", "(", "~", "5", ")", ")", "&", "f", "(", "2", "*", "(", "0", ",", "1", ")", ")", "^", "m", "(", "0", ",",
        "1", ")", ";"
      ])
    );
    assert_eq!(
      macro_set.parse_var_macro("line3"),
      Ok(tokens!["int", "i", "[", "]", "=", "{", "1", ",", "23", ",", "4", ",", "5", ",", "}", ";"])
    );
    assert_eq!(
      macro_set.parse_var_macro("line4"),
      Ok(tokens!["char", "c", "[", "2", "]", "[", "6", "]", "=", "{", "\"hello\"", ",", "\"\"", "}", ";"])
    );
  }
}
