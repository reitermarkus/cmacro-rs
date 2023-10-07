// These two should produce the same output, but the second one is initially parsed
// as nested casts instead of a multiplication due to the extra parentheses.
#define pdMS_TO_TICKS_NO_PAR(xTimeInMs)    ( ( TickType_t )   xTimeInMs   * ( TickType_t ) configTICK_RATE_HZ ) / ( TickType_t ) 1000U
#define pdMS_TO_TICKS(xTimeInMs)           ( ( TickType_t ) ( xTimeInMs ) * ( TickType_t ) configTICK_RATE_HZ ) / ( TickType_t ) 1000U
