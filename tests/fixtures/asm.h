#define secureportREAD_PSP( pucOutCurrentStackPointer ) \
  __asm volatile ( "mrs %0, psp"  : "=r" ( pucOutCurrentStackPointer ) )

#define secureportSET_PSP( pucCurrentStackPointer ) \
  __asm volatile ( "msr psp, %0" : : "r" ( pucCurrentStackPointer ) )


#define i386_example1(old, base, offset) __asm__ (\
    "btsl %2,%1\n\t" \
    "sbb %0,%0"  \
    : "=r" (old), "+rm" (*base) \
    : "Ir" (offset) \
    : "cc" \
  );

#define i386_example2(src, dst) asm (\
    "mov %1, %0\n\t" \
    "add $1, %0" \
    : "=r" (dst) \
    : "r" (src) \
  );

#define vax_example(from, to, count) asm volatile ( \
    "movc3 %0, %1, %2" \
    : /* No outputs. */ \
    : "g" (from), "g" (to), "g" (count) \
    : "r0", "r1", "r2", "r3", "r4", "r5", "memory" \
  );

#define func() \
  __asm__ (".globl func\n\t" \
             ".type func, @function\n\t" \
             "func:\n\t" \
             ".cfi_startproc\n\t" \
             "movl $7, %eax\n\t" \
             "ret\n\t" \
             ".cfi_endproc");

#define times5(n) \
  __asm__ ("leal (%0,%0,4),%0" \
           : "=r" (n) \
           : "0" (n));
