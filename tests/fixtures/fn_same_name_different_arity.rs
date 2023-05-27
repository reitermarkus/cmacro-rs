#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__func {
  ($x:expr) => {
    func(($x).into(), 3)
  };
}
pub use __cmacro__func as func;
