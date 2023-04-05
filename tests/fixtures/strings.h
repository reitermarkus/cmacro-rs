// Non-UTF8 string.
#define s1 "\xff"

// Concatenated string.
#define s2 s1 s1

// Concatenated identifier and string.
#define s3 s ## 1 s1

// Normal string literal.
#define HELLO1 "WORLD"
#define HELLO2 (char* const)"WORLD"

// Cast string.
#define CAST_STRING (int*)"STRINGINT"

// UTF-8 string prefix.
#define UTF8 u8"UTF-8"

// UTF-16 string prefix.
#define UTF16 u"UTF-16"

// UTF-32 string prefix.
#define UTF32 U"UTF-32"

// Wide string prefix.
#define WIDE L"WIDE"
