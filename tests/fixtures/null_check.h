// NOTE: This is usually defined in `stddef.h`.
#define NULL (void*)0

#define IS_NULL(ptr) ptr == NULL
#define IS_NONNULL(ptr) ptr != NULL
