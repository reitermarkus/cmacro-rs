#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f1 {
  ($x:expr) => {
    $x * 2
  };
}
pub use __cmacro__f1 as f1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f2 {
  ($y:expr) => {
    $y * ($y * 2)
  };
}
pub use __cmacro__f2 as f2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__f4 {
  ($x:expr, $y:expr, $z:expr) => {
    ($x + $y) * $z
  };
}
pub use __cmacro__f4 as f4;
