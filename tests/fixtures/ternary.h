#define OK 0

#define IS_OK(val) val == OK ? true : false

#define ZERO_OR_EVEN(val) val == 0 ? true : val % 2 == 0 ? true : false

#define TERNARY_PRECEDENCE1 1 ? 2 : 3 == 3
#define TERNARY_PRECEDENCE2 1 ? 2 : (3 == 3) // Same as above.
#define TERNARY_PRECEDENCE3 (1 ? 2 : 3) == 3
