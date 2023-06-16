#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__offsetof {
  ($type:ty, $member:tt) => {
    mem::offsetof!($type, $member)
  };
}
pub use __cmacro__offsetof as offsetof;

