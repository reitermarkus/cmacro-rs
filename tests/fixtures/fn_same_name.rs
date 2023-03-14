#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__func {
  ($x:expr) => {
    func(($x).into())
  };
}
pub use __cmacro__func as func;
