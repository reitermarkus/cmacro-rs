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
