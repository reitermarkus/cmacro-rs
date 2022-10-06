// Non-UTF8 string.
#define s1 "\xff"

// Concatenated string.
#define s2 s1 s1

// Concatenated identifier and string.
#define s3 s ## 1 s1

// Normal string literal.
#define HELLO1 "WORLD"
#define HELLO2 (char* const)"WORLD"
