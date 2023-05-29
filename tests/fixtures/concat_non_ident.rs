// FIXME: The `concat_idents!` macro currently does not support numbers.
//
// #[doc(hidden)]
// #[macro_export]
// macro_rules! __cmacro__CONCAT_123 {
//   ($var:ident) => {
//     concat_idents!($var, 123)
//   };
// }
// pub use __cmacro__CONCAT_123 as CONCAT_123;
//
// #[doc(hidden)]
// #[macro_export]
// macro_rules! __cmacro__CONCAT_123DEF {
//   ($var:ident) => {
//     concat_idents!($var, 123, def)
//   };
// }
// pub use __cmacro__CONCAT_123DEF as CONCAT_123DEF;
//
// #[doc(hidden)]
// #[macro_export]
// macro_rules! __cmacro__CONCAT_123DEF456GHI {
//   ($var:ident) => {
//     concat_idents!($var, 123, def456ghi)
//   };
// }
// pub use __cmacro__CONCAT_123DEF456GHI as CONCAT_123DEF456GHI;
