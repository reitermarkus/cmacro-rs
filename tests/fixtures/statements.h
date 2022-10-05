#define vTaskDelayUntil(pxPreviousWakeTime, xTimeIncrement)      \
  do {                                                             \
    (void)xTaskDelayUntil((pxPreviousWakeTime), (xTimeIncrement)); \
  } while(0)

#define pdFALSE 0

#define portEND_SWITCHING_ISR( xSwitchRequired ) \
  if (xSwitchRequired != pdFALSE) vPortYield()

#define JSVAL_TAG_MAX_DOUBLE         ((uint32_t)(0x1FFF0))
#define JSVAL_TAG_SHIFT 47
#define JSVAL_TYPE_TO_TAG(type)      ((JSValueTag)(JSVAL_TAG_MAX_DOUBLE | (type)))
#define JSVAL_TYPE_TO_SHIFTED_TAG(type) (((uint64_t)JSVAL_TYPE_TO_TAG(type)) << JSVAL_TAG_SHIFT)
