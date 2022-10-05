// Simply function with one argument.
#define f1(x) x * 2

// Function calling another function.
#define f2(y) y * f1(y)

// Variable alias.
#define y x

// Unused function argument with variables aliased to the name of that argument,
// i.e. the two `x`s should be different variables.
#define f3(x) y + y
