// Non-UTF8 string.
#define s1 "\xff"

/// Concatenated string.
#define s2 s1 s1

/// Concatenated identifier and string.
#define s3 s ## 1 s1

#define MY_DONUT1 U'\U0001f369'
#define MY_DONUT1 U'🍩'
