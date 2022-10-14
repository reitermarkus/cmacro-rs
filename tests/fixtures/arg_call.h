#define F() 777

// This should not expand to `777`, since the `F` refers to the
// argument `F` rather than the macro definition `F` above.
#define ARG_CALL(F) F()
