#define __int_c_join(a, b) a ## b
#define __int_c(v, suffix) __int_c_join(v, suffix)
#define __uint_c(v, suffix) __int_c_join(v##U, suffix)

#define UINT64_C(v) __uint_c(v, __int64_c_suffix)
