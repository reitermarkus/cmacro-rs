void func(int, int);

#define func(x) func(x, 3)

// NOTE: This macro is invalid, because it does not call the `func` function, but expands the `func` macro with two arguments.
#define wrapper_func(x) func(x, 3)
