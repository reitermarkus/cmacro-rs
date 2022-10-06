macro_rules! __STRING {
  ($x:expr) => {
    concat!(stringify!($x), '\0').as_ptr() as *const c_char
  };
}

macro_rules! DOUBLE_STRING {
  ($x:expr) => {
    concat!(stringify!($x), stringify!($x), '\0').as_ptr() as *const c_char
  };
}
