#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__func {
  ($x:expr) => {
    func(($x).into())
  };
}
pub use __cmacro__func as func;

#[allow(non_snake_case, unused_mut, unsafe_code)]
#[inline(always)]
pub unsafe extern "C" fn wrapper_func(mut x: c_int) {
  func(x);
}
