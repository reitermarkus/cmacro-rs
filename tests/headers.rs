use std::{collections::HashMap, env, fs, process::exit};

use clang::{source::SourceRange, Clang, EntityKind, EntityVisitResult, Index};
use glob::glob;
use pretty_assertions::StrComparison;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};
use yansi::{
  Color::{Green, Red},
  Style,
};

use cmacro::{CodegenContext, ExpansionError, FnMacro, MacroSet, VarMacro};

fn location_in_scope(r: &SourceRange) -> bool {
  let start = r.get_start();
  let location = start.get_spelling_location();
  start.is_in_main_file() && !start.is_in_system_header() && location.file.is_some()
}

fn file_visit_macros<F: FnMut(EntityKind, &str, Option<&[&str]>, &[&str])>(file: &str, mut visitor: F) {
  let clang = Clang::new().unwrap();

  let index = Index::new(&clang, false, true);

  let tu = index
    .parser(file)
    .arguments(&["-std=c11"])
    .detailed_preprocessing_record(true)
    .skip_function_bodies(true)
    .parse()
    .unwrap();

  let entity = tu.get_entity();
  entity.visit_children(|cur, _parent| {
    let range = cur.get_range().unwrap();
    if !location_in_scope(&range) {
      return EntityVisitResult::Continue
    }

    match cur.get_kind() {
      kind @ EntityKind::FunctionDecl => {
        let mut tokens = range.tokenize().into_iter().map(|token| token.get_spelling());

        let return_type = tokens.next().unwrap();
        let name = tokens.next().unwrap();
        tokens.next();
        let args = tokens.take_while(|token| token != ")").collect::<Vec<_>>();
        let args = args.iter().map(|t| t.as_str()).collect::<Vec<&str>>();

        visitor(kind, &name, Some(args).as_deref(), &[&return_type])
      },
      kind @ EntityKind::MacroDefinition => {
        let range = cur.get_range().unwrap();
        if !location_in_scope(&range) {
          return EntityVisitResult::Continue
        }

        let mut tokens: Vec<_> = range.tokenize().into_iter().map(|token| token.get_spelling()).collect();

        let name = tokens.remove(0);

        let args = if cur.is_function_like_macro() {
          let n = tokens.iter().position(|t| t == ")").unwrap();

          let args = tokens.drain(0..(n + 1)).skip(1).take(n - 1).filter(|t| t != ",").collect::<Vec<_>>();

          Some(args)
        } else {
          None
        };

        let args = args.as_ref().map(|args| args.iter().map(|t| t.as_str()).collect::<Vec<&str>>());
        let tokens = tokens.iter().map(|t| t.as_str()).collect::<Vec<&str>>();

        visitor(kind, &name, args.as_deref(), &tokens)
      },
      _ => (),
    }

    EntityVisitResult::Continue
  });
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
  let test_name: Option<String> = env::args().nth(1);

  let mut errors = HashMap::new();

  for entry in glob("./tests/fixtures/*.h").unwrap() {
    let entry = entry?;
    let header_name = entry.as_path().file_stem().and_then(|s| s.to_str()).unwrap();
    let header_path = entry.as_path().display().to_string();
    let output_path = entry.as_path().with_extension("rs");

    if let Some(ref test_name) = test_name {
      if !test_name.starts_with('-') && !header_name.contains(test_name) {
        continue
      }
    }

    print!("test {} ... ", header_name);

    #[derive(Debug, Default)]
    struct Context {
      pub macros: Vec<String>,
      pub functions: HashMap<String, (Vec<String>, String)>,
      pub fn_macros: HashMap<String, FnMacro>,
      pub var_macros: HashMap<String, VarMacro>,
      pub macro_set: MacroSet,
    }

    impl CodegenContext for Context {
      fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
        self.functions.get(name).cloned()
      }
    }

    let mut context = Context::default();

    file_visit_macros(&header_path, |kind, name, args, value| match kind {
      EntityKind::FunctionDecl => {
        context.functions.insert(
          name.to_owned(),
          (args.unwrap().iter().map(|&token| token.to_owned()).collect(), value[0].to_owned()),
        );
      },
      EntityKind::MacroDefinition => {
        if let Some(args) = args {
          context.macro_set.define_fn_macro(name, args, value);
        } else {
          context.macro_set.define_var_macro(name, value);
        }

        context.macros.push(name.to_owned());
      },
      _ => (),
    });

    let mut f = TokenStream::new();

    for name in &context.macros {
      match context.macro_set.expand_fn_macro(name) {
        Ok(fn_macro) => {
          let arg_names = context.macro_set.fn_macro_args(name).unwrap();
          let arg_names2 = arg_names
            .iter()
            .map(|s| if s == "..." { "$__VA_ARGS__".to_owned() } else { format!("${s}") })
            .collect::<Vec<_>>();
          let arg_names2 = arg_names2.iter().map(|s| s.as_ref()).collect::<Vec<_>>();
          let arg_names = arg_names.iter().map(|s| s.as_ref()).collect::<Vec<_>>();
          let body = fn_macro
            .iter()
            .map(|t| match t {
              cmacro::MacroToken::Arg(i) => arg_names2[*i],
              cmacro::MacroToken::Token(s) => s.as_ref(),
            })
            .collect::<Vec<_>>();

          match FnMacro::parse(name.as_str(), &arg_names, &body) {
            Ok(mut fn_macro) => {
              if let Ok(tokens) = fn_macro.generate(&context) {
                f.append_all(tokens);
              }
            },
            Err(err) => eprintln!("Error parsing function-like macro {name}: {err}"),
          }
        },
        Err(ExpansionError::MacroNotFound) => (),
        Err(err) => eprintln!("Error for {name}: {err:?}"),
      }

      match context.macro_set.expand_var_macro(name) {
        Ok(var_macro) => {
          let body = var_macro
            .iter()
            .map(|t| match t {
              cmacro::MacroToken::Arg(_) => unreachable!(),
              cmacro::MacroToken::Token(s) => s.as_ref(),
            })
            .collect::<Vec<_>>();

          match VarMacro::parse(name.as_str(), &body) {
            Ok(mut var_macro) => {
              if let Ok((value, ty)) = var_macro.generate(&context) {
                let name = Ident::new(name, Span::call_site());
                let ty = ty.unwrap_or(quote! { _ });
                f.append_all(quote! {
                  pub const #name: #ty = #value;
                })
              }
            },
            Err(err) => eprintln!("Error parsing variable-like macro {name}: {err}"),
          }
        },
        Err(ExpansionError::MacroNotFound) => (),
        Err(err) => eprintln!("Error for {name}: {err:?}"),
      }
    }

    let expected = prettyplease::unparse(&syn::parse2::<syn::File>(f)?);
    let actual = prettyplease::unparse(&syn::parse_str::<syn::File>(&fs::read_to_string(output_path)?)?);

    if actual == expected {
      println!(" {}", Style::new(Green).paint("ok"));
    } else {
      println!(" {}", Style::new(Red).paint("FAILED"));
      errors.insert(header_name.to_owned(), (actual, expected));
    }
  }

  if !errors.is_empty() {
    println!("\nfailures:\n");

    for (header_name, (actual, expected)) in &errors {
      let diff = StrComparison::new(expected, actual);
      print!("---- {} diff ----\n{}", header_name, diff);
    }

    println!("\nfailures:");

    for header_name in errors.keys() {
      println!("    {}", header_name);
    }

    println!();
    exit(1);
  }

  Ok(())
}
