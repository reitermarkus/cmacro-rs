#define PTR (*((volatile int *)0xdeafbeef))

#define ASSIGN()     PTR = 42;
#define ADD_ASSIGN() PTR += 42;
#define INC()        ++PTR;
#define POST_INC()   PTR++;
#define DEC()        --PTR;
#define POST_DEC()   PTR--;
