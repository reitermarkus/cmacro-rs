#define FLASH_SIZE_DATA_REGISTER ((uint32_t)0x1FFF75E0)

// This cannot be represented as a variable since the dereference
// must happen at runtime.
#define FLASH_SIZE1 *((uint16_t *)FLASH_SIZE_DATA_REGISTER)

#define FLASH_SIZE2() *((uint16_t *)FLASH_SIZE_DATA_REGISTER)
