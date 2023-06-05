#define _REENT_INIT_PTR_ZEROED(var) \
  { (var)->_stdin = &__sf[0]; \
    (var)->_stdout = &__sf[1]; \
    (var)->_stderr = &__sf[2]; \
  }

#define ARRAY_ACCESS(a) a[0]

#define ARRAY_FIELD_ACCESS(a) a[0].field

#define FIELD_ARRAY_ACCESS(a) a.field[0]

#define NESTED_ARRAY_ACCESS(a) a[1][2]

#define NESTED_ARRAY_ACCESS_CONVOLUTED(a) (*(&a[1]))[2]
