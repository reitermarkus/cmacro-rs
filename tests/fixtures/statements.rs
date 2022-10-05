macro_rules! vTaskDelayUntil {
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

pub const pdFALSE: _ = 0;

macro_rules! portEND_SWITCHING_ISR {
  ($xSwitchRequired:expr) => {
    if ($xSwitchRequired != 0) {
      vPortYield();
    }
  };
}

pub const JSVAL_TAG_MAX_DOUBLE: uint32_t = 131056 as uint32_t;

pub const JSVAL_TAG_SHIFT: _ = 47;

macro_rules! JSVAL_TYPE_TO_TAG {
  ($type:expr) => {
    (131056 as uint32_t | $type) as JSValueTag
  };
}

macro_rules! JSVAL_TYPE_TO_SHIFTED_TAG {
  ($type:expr) => {
    (((131056 as uint32_t | $type) as JSValueTag as uint64_t) << 47)
  };
}
