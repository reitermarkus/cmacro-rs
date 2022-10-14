use std::{collections::HashMap, mem};

/// Interpolate var macros in other macros.
fn interpolate_var_macros<'t>(
  macro_name: &str,
  macro_args: Option<&HashMap<&'t str, Option<&[&'t str]>>>,
  tokens: &[&'t str],
  var_macros: &HashMap<&str, Vec<&'t str>>,
  fn_macros: &HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
) -> Vec<&'t str> {
  fn interpolate_var_macros_inner<'t>(
    start_name: &str,
    macro_name: &str,
    macro_args: Option<&HashMap<&'t str, Option<&[&'t str]>>>,
    tokens: &[&'t str],
    var_macros: &HashMap<&str, Vec<&'t str>>,
    fn_macros: &HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
  ) -> Vec<&'t str> {
    let mut output = vec![];

    let mut it = tokens.iter().peekable();

    while let Some(token) = it.next() {
      if let Some(tokens) = macro_args.and_then(|args| args.get(token)) {
        if let Some(tokens) = tokens {
          output.extend(*tokens);
        } else {
          output.push(*token);
        }

        continue
      }

      // Don't interpolate self or function-like macro arguments.
      if *token == start_name || *token == macro_name {
        output.push(*token);
        continue
      }

      // Don't interpolate stringification or identifier concatenation.
      if *token == "#" || *token == "##" {
        output.push(token);
        if let Some(token) = it.next() {
          output.push(token);
        }

        continue
      }

      // Don't interpolate identifier concatenation.
      if it.peek() == Some(&&"##") {
        output.push(token);
        continue
      }

      if let Some((fn_args, tokens)) = fn_macros.get(token) {
        let mut paren_level = 0;

        let mut args = vec![];

        let mut jt = it.clone();
        let mut arg = vec![];

        for token in &mut jt {
          if *token == "(" {
            if paren_level != 0 {
              arg.push(*token);
            }

            paren_level += 1;
          } else if *token == ")" {
            paren_level -= 1;

            if paren_level == 0 {
              args.push(mem::take(&mut arg));
            } else {
              arg.push(*token);
            }
          } else if *token == "," && paren_level == 1 {
            args.push(mem::take(&mut arg))
          } else {
            arg.push(*token);
          }

          if paren_level == 0 {
            break
          }
        }

        if args.len() == fn_args.len() {
          let args = args
            .into_iter()
            .map(|arg| interpolate_var_macros_inner(start_name, token, None, &arg, var_macros, fn_macros))
            .collect::<Vec<_>>();

          let args = fn_args
            .iter()
            .zip(args.iter())
            .map(|(&name, arg)| (name, Some(arg.as_slice())))
            .collect::<HashMap<&str, Option<&[&str]>>>();

          it = jt;
          output.extend(interpolate_var_macros_inner(start_name, token, Some(&args), tokens, var_macros, fn_macros));
          continue
        }
      }

      if let Some(tokens) = var_macros.get(token) {
        output.extend(interpolate_var_macros_inner(start_name, token, None, tokens, var_macros, fn_macros))
      } else {
        output.push(token);
      }
    }

    output
  }

  interpolate_var_macros_inner(macro_name, macro_name, macro_args, tokens, var_macros, fn_macros)
}

/// Expand macros.
///
/// Interpolates nested macro usages in unparsed macro token streams.
///
/// This is needed to be able to parse cases such as the following:
///
/// ```c
/// #define THREE_PLUS 3 +
/// #define FOUR 4
/// #define THREE_PLUS_FOUR THREE_PLUS FOUR
/// ```
///
/// [`VarMacro::parse`](crate::VarMacro::parse) cannot parse `THREE_PLUS` since it is not a
/// valid expression. This would lead to `THREE_PLUS_FOUR` also not being able to be parsed.
///
/// # Caveats
///
/// Currently, this is not yet usable since expanding the following is wrong:
///
/// ```c
/// #define B A
/// #define F(A) A + B
/// ```
///
/// `A + B` would be expanded to `A + A`. The first `A` is corresponds to the macro argument `A`, while
/// the second `A` corresponds to an unbound variable, i.e. the two `A`s should be treated as
/// different variables.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
///
/// let mut var_macros = HashMap::from([
///   ("A", vec!["1"]),
///   ("B", vec!["2"]),
///   ("PLUS", vec!["A", "+", "B"]),
///   ("A_TIMES_B", vec!["TIMES", "(", "A", ",", "B", ")"]),
///   ("A_PLUS", vec!["A", "+"]),
///   ("A_PLUS_CONCAT_B", vec!["A_PLUS", "B"]),
/// ]);
/// let mut fn_macros = HashMap::from([
///   ("TIMES", (vec!["A", "B"], vec!["A", "*", "B"])),
///   ("TIMES_B", (vec!["A"], vec!["A", "*", "B"])),
/// ]);
///
/// cmacro::expand(&mut var_macros, &mut fn_macros);
///
/// let expanded_var_macros = HashMap::from([
///   ("A", vec!["1"]),
///   ("B", vec!["2"]),
///   ("PLUS", vec!["1", "+", "2"]),
///   ("A_TIMES_B", vec!["1", "*", "2"]),
///   ("A_PLUS", vec!["1", "+"]),
///   ("A_PLUS_CONCAT_B", vec!["1", "+", "2"]),
/// ]);
/// let expanded_fn_macros = HashMap::from([
///   ("TIMES", (vec!["A", "B"], vec!["A", "*", "B"])),
///   ("TIMES_B", (vec!["A"], vec!["A", "*", "2"])),
/// ]);
///
/// assert_eq!(var_macros, expanded_var_macros);
/// assert_eq!(fn_macros, expanded_fn_macros);
/// ```
pub fn expand<'t>(
  var_macros: &mut HashMap<&str, Vec<&'t str>>,
  fn_macros: &mut HashMap<&str, (Vec<&'t str>, Vec<&'t str>)>,
) {
  // Interpolate variable macros in variable macros.
  let var_macro_names = var_macros.keys().cloned().collect::<Vec<_>>();
  for macro_name in var_macro_names {
    let tokens = var_macros.get(macro_name).unwrap();
    let tokens = interpolate_var_macros(macro_name, None, tokens, var_macros, fn_macros);
    var_macros.insert(macro_name, tokens);
  }

  // Interpolate variable macros in function macros.
  let fn_macro_names = fn_macros.keys().cloned().collect::<Vec<_>>();
  for macro_name in fn_macro_names {
    let (args, tokens) = fn_macros.remove(macro_name).unwrap();
    let arg_names =
      args.iter().zip(args.iter()).map(|(&arg, _)| (arg, None)).collect::<HashMap<&str, Option<&[&str]>>>();
    let tokens = interpolate_var_macros(macro_name, Some(&arg_names), &tokens, var_macros, fn_macros);
    fn_macros.insert(macro_name, (args, tokens));
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn var_macros() {
    let var_macros = HashMap::from([
      ("A", vec!["1"]),
      ("B", vec!["2"]),
      ("PLUS", vec!["A", "+", "B"]),
      ("CONCAT", vec!["A", "##", "B"]),
      ("STRINGIFY", vec!["#", "A"]),
    ]);

    let fn_macros = HashMap::new();

    let plus = interpolate_var_macros("PLUS", None, var_macros.get("PLUS").unwrap(), &var_macros, &fn_macros);
    assert_eq!(plus, vec!["1", "+", "2"]);

    let concat = interpolate_var_macros("CONCAT", None, var_macros.get("CONCAT").unwrap(), &var_macros, &fn_macros);
    assert_eq!(concat, vec!["A", "##", "B"]);

    let stringify =
      interpolate_var_macros("STRINGIFY", None, var_macros.get("STRINGIFY").unwrap(), &var_macros, &fn_macros);
    assert_eq!(stringify, vec!["#", "A"]);
  }
}
