#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f1__ {
  ($x:expr) => {
    ($x * 2)
  };
}
#[doc(inline)]
pub use __cmacro__f1__ as f1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f2__ {
  ($y:expr) => {
    ($y * ($y * 2))
  };
}
#[doc(inline)]
pub use __cmacro__f2__ as f2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f4__ {
  ($x:expr, $y:expr, $z:expr) => {
    (($x + $y) * $z)
  };
}
#[doc(inline)]
pub use __cmacro__f4__ as f4;
