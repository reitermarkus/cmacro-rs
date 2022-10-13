#define secureportREAD_PSP( pucOutCurrentStackPointer ) \
    __asm volatile ( "mrs %0, psp"  : "=r" ( pucOutCurrentStackPointer ) )

#define secureportSET_PSP( pucCurrentStackPointer ) \
    __asm volatile ( "msr psp, %0" : : "r" ( pucCurrentStackPointer ) )
