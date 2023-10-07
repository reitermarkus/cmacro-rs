#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__pdMS_TO_TICKS_NO_PAR {
  ($xTimeInMs:expr) => {
    $xTimeInMs as TickType_t * configTICK_RATE_HZ as TickType_t / 1000u16 as TickType_t
  };
}
pub use __cmacro__pdMS_TO_TICKS_NO_PAR as pdMS_TO_TICKS_NO_PAR;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__pdMS_TO_TICKS {
  ($xTimeInMs:expr) => {
    $xTimeInMs as TickType_t * configTICK_RATE_HZ as TickType_t / 1000u16 as TickType_t
  };
}
pub use __cmacro__pdMS_TO_TICKS as pdMS_TO_TICKS;
