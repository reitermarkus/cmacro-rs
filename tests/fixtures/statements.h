#define vTaskDelayUntil(pxPreviousWakeTime, xTimeIncrement)      \
  do {                                                             \
    (void)xTaskDelayUntil((pxPreviousWakeTime), (xTimeIncrement)); \
  } while(0)

#define pdFALSE 0

#define portEND_SWITCHING_ISR( xSwitchRequired ) \
  if (xSwitchRequired != pdFALSE) vPortYield()
