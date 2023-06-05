#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__PREV {
  ($x:expr) => {
    * $x.sub(1)
  };
}
pub use __cmacro__PREV as PREV;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__NEXT {
  ($x:expr) => {
    * $x.add(1)
  };
}
pub use __cmacro__NEXT as NEXT;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__NEXT_INC {
  ($x:expr) => {
    *{ $x = $x.add(1); $x }
  };
}
pub use __cmacro__NEXT_INC as NEXT_INC;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__CURR_INC {
  ($x:expr) => {
    *{ let prev = $x; $x = $x.add(1); prev }
  };
}
pub use __cmacro__CURR_INC as CURR_INC;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__PREV_DEC {
  ($x:expr) => {
    *{ $x = $x.sub(1); $x }
  };
}
pub use __cmacro__PREV_DEC as PREV_DEC;
#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__CURR_DEC {
  ($x:expr) => {
    *{ let prev = $x; $x = $x.sub(1); prev }
  };
}
pub use __cmacro__CURR_DEC as CURR_DEC;
