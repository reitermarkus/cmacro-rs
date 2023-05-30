// Non-UTF8 string.
#define s1 "\xff"

// Concatenated string.
#define s2 s1 s1

// Concatenated identifier and string.
#define s3 s ## 1 s1

// Normal string literal.
#define HELLO1 "WORLD"
#define HELLO2 (char* const)"WORLD"
#define HELLO3() "!"

// Cast string.
#define CAST_STRING (int*)"STRINGINT"

// UTF-8 string prefix.
#define UTF8 u8"UTF-8"
#define UTF8_FN() u8"UTF-8"

// Concatenated UTF-8 string.
#define UTF8_CONCAT u8"UTF-8" " and then some"
#define UTF8_CONCAT_UTF8 u8"UTF-8" u8" and then some"

// UTF-16 string prefix.
#define UTF16 u"UTF-16"
#define UTF16_FN() u"UTF-16"

// Concatenated UTF-16 string.
#define UTF16_CONCAT u"UTF-16" "and then some"
#define UTF16_CONCAT_UTF16 u"UTF-16" u"and then some"

// UTF-32 string prefix.
#define UTF32 U"UTF-32"
#define UTF32_FN() U"UTF-32"

// Concatenated UTF-16 string.
#define UTF32_CONCAT U"UTF-32" "and then some"
#define UTF32_CONCAT_UTF32 U"UTF-32" U"and then some"

// Wide string prefix.
#define WIDE L"WIDE"
#define WIDE_FN() L"WIDE"

// Concatenated wide string.
#define WIDE_CONCAT L"WIDE" "and then some"
#define WIDE_CONCAT_WIDE L"WIDE" L"and then some"

// Ordinary string with and without escape sequences.
#define ORDINARY_BANANA1 "a猫🍌"
#define ORDINARY_BANANA2 "a\u732B\U0001F34C"

// UTF-8 string with and without escape sequences.
#define UTF8_BANANA1 u8"a猫🍌"
#define UTF8_BANANA2 u8"a\u732B\U0001F34C"

// UTF-16 string with and without escape sequences.
#define UTF16_BANANA1 u"a猫🍌"
#define UTF16_BANANA2 u"a\u732B\U0001F34C"

// UTF-32 string with and without escape sequences.
#define UTF32_BANANA1 U"a猫🍌"
#define UTF32_BANANA2 U"a\u732B\U0001F34C"

// Wide string with and without escape sequences.
#define WIDE_BANANA1 L"a猫🍌"
#define WIDE_BANANA2 L"a\u732B\U0001F34C"
