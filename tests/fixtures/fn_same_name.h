void func(int);

#define func(x) func(x)

#define wrapper_func(x) func(x)
