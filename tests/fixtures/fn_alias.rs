#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__A {
  () => {
    123
  };
}
pub use __cmacro__A as A;

pub const B: _ = A;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__C {
  () => {
    123
  };
}
pub use __cmacro__C as C;
