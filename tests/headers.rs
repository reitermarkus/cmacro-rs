use std::{collections::HashMap, fs};

use clang::{source::SourceRange, Clang, EntityKind, EntityVisitResult, Index};
use glob::glob;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use cmacro::{CodegenContext, FnMacro, VarMacro};

fn location_in_scope(r: &SourceRange) -> bool {
  let start = r.get_start();
  let location = start.get_spelling_location();
  start.is_in_main_file() && !start.is_in_system_header() && location.file.is_some()
}

fn file_visit_macros<F: FnMut(&str, Option<&[&str]>, &[&str])>(file: &str, mut visitor: F) {
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
    if cur.get_kind() == EntityKind::MacroDefinition {
      let range = cur.get_range().unwrap();
      if !location_in_scope(&range) {
        return EntityVisitResult::Continue
      }

      let mut tokens: Vec<_> = range.tokenize().into_iter().filter_map(|token| Some(token.get_spelling())).collect();

      let name = tokens.remove(0);

      let args = if cur.is_function_like_macro() {
        let n = tokens.iter().position(|t| t == ")").unwrap();

        let args = tokens.drain(0..(n + 1)).skip(1).take(n - 1).filter(|t| t != ",").collect::<Vec<_>>();

        Some(args)
      } else {
        None
      };

      let args =
        if let Some(args) = &args { Some(args.into_iter().map(|t| t.as_str()).collect::<Vec<&str>>()) } else { None };
      let tokens = tokens.iter().map(|t| t.as_str()).collect::<Vec<&str>>();

      visitor(&name, args.as_deref(), &tokens)
    }

    EntityVisitResult::Continue
  });
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
  for entry in glob("./tests/fixtures/*.h").unwrap() {
    let entry = entry?;
    let header_path = entry.as_path().display().to_string();
    let output_path = entry.as_path().with_extension("rs");

    #[derive(Debug, Clone, Default)]
    struct Context {
      pub macros: Vec<String>,
      pub fn_macros: HashMap<String, FnMacro>,
      pub var_macros: HashMap<String, VarMacro>,
    }

    impl CodegenContext for Context {
      fn function_macro(&self, name: &str) -> Option<&FnMacro> {
        self.fn_macros.get(name)
      }

      fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
        self.var_macros.get(name)
      }
    }

    let mut context = Context::default();

    file_visit_macros(&header_path, |name, args, value| {
      if let Some(args) = args {
        context.fn_macros.insert(name.to_owned(), FnMacro::parse(name, args, value).unwrap());
      } else {
        context.var_macros.insert(name.to_owned(), VarMacro::parse(name, value).unwrap());
      }

      context.macros.push(name.to_owned());
    });

    let mut f = TokenStream::new();

    for name in &context.macros {
      if let Some(fn_macro) = context.function_macro(name) {
        let mut fn_macro = fn_macro.clone();
        if let Ok(tokens) = fn_macro.generate(&context) {
          f.append_all(tokens);
        }
      }

      if let Some(var_macro) = context.variable_macro(name) {
        let mut var_macro = var_macro.clone();
        if let Ok((value, ty)) = var_macro.generate(&context) {
          let name = Ident::new(name, Span::call_site());
          let ty = ty.unwrap_or(quote! { _ });
          f.append_all(quote! {
            pub const #name: #ty = #value;
          })
        }
      }
    }

    let output = fs::read_to_string(output_path)?.parse::<TokenStream>()?;

    assert_eq!(f.to_string(), output.to_string());
  }

  Ok(())
}
