#define portYIELD()                                 \
{                                                   \
    /* Set a PendSV to request a context switch. */ \
    portNVIC_INT_CTRL_REG = portNVIC_PENDSVSET_BIT; \
    __asm( "	dsb");                                \
    __asm( "	isb");                                \
}

#define portNVIC_INT_CTRL_REG ( *( ( volatile uint32_t * ) 0xe000ed04 ) )
#define portNVIC_PENDSVSET_BIT    ( 1UL << 28UL )
