#define LINE_VAR __LINE__
#define LINE() LINE_VAR

#define FILE_VAR __FILE__
#define FILE() FILE_VAR

#define STRINGIFY(s) #s
#define STRINGIFY2(s) STRINGIFY(s)
#define LINE_AND_FILE() FILE() STRINGIFY2(__LINE__)

#define STRINGIFY_FILE() STRINGIFY2(__FILE__)
