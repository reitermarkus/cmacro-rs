pub const OK: _ = 0;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__IS_OK {
  ($val:expr) => {
    if $val == 0 { true } else { false }
  };
}
pub use __cmacro__IS_OK as IS_OK;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__ZERO_OR_EVEN {
  ($val:expr) => {
    if $val == 0 {
      true
    } else {
      if $val % 2 == 0 {
        true
      } else {
        false
      }
    }
  };
}
pub use __cmacro__ZERO_OR_EVEN as ZERO_OR_EVEN;

pub const TERNARY_PRECEDENCE1: bool = if 1 != 0 { 2 } else { 3 == 3 };
pub const TERNARY_PRECEDENCE2: bool = if 1 != 0 { 2 } else { 3 == 3 };
pub const TERNARY_PRECEDENCE3: bool = if 1 != 0 { 2 } else { 3 } == 3;
