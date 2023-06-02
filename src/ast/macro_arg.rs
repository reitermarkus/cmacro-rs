/// A macro argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroArg {
  pub(crate) index: usize,
}

impl MacroArg {
  /// Create a new macro argument with the given index.
  pub fn new(index: usize) -> Self {
    Self { index }
  }
}

impl MacroArg {
  pub(crate) fn index(&self) -> usize {
    self.index
  }
}
