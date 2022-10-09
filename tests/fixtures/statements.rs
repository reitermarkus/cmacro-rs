#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__vTaskDelayUntil__ {
  ($pxPreviousWakeTime:expr, $xTimeIncrement:expr) => {
    loop {
      {
        drop(xTaskDelayUntil(($pxPreviousWakeTime).into(), ($xTimeIncrement).into()))
      };

      if 0 == Default::default() {
        break
      }
    }
  };
}
#[doc(inline)]
pub use self::__cmacro__vTaskDelayUntil__ as vTaskDelayUntil;

pub const pdFALSE: _ = 0;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__portEND_SWITCHING_ISR__ {
  ($xSwitchRequired:expr) => {
    if $xSwitchRequired != 0 {
      vPortYield();
    }
  };
}
#[doc(inline)]
pub use self::__cmacro__portEND_SWITCHING_ISR__ as portEND_SWITCHING_ISR;

pub const JSVAL_TAG_MAX_DOUBLE: uint32_t = 131056 as uint32_t;

pub const JSVAL_TAG_SHIFT: _ = 47;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__JSVAL_TYPE_TO_TAG__ {
  ($type:expr) => {
    (131056 as uint32_t | $type) as JSValueTag
  };
}
#[doc(inline)]
pub use self::__cmacro__JSVAL_TYPE_TO_TAG__ as JSVAL_TYPE_TO_TAG;

#[doc(hidden)]
#[macro_export]
macro_rules! __cmacro__JSVAL_TYPE_TO_SHIFTED_TAG__ {
  ($type:expr) => {
    (131056 as uint32_t | $type) as JSValueTag as uint64_t << 47
  };
}
#[doc(inline)]
pub use self::__cmacro__JSVAL_TYPE_TO_SHIFTED_TAG__ as JSVAL_TYPE_TO_SHIFTED_TAG;
