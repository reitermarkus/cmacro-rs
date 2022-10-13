#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__prec_rem_div1 {
  ($ a : expr , $ b : expr , $ c : expr) => {
    $a % $b / $c
  };
}
pub use __cmacro__prec_rem_div1 as prec_rem_div1;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__prec_rem_div2 {
  ($ a : expr , $ b : expr , $ c : expr) => {
    $a % $b / $c
  };
}
pub use __cmacro__prec_rem_div2 as prec_rem_div2;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__prec_rem_div3 {
  ($ a : expr , $ b : expr , $ c : expr) => {
    $a % ($b / $c)
  };
}
pub use __cmacro__prec_rem_div3 as prec_rem_div3;
