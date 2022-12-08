pub const PERIPH_BASE: uint32_t = 1073741824 as uint32_t;
pub const APB2PERIPH_BASE: uint32_t = 1073741824 as uint32_t + 65536;
pub const SYSCFG_BASE: uint32_t = 1073741824 as uint32_t + 65536 + 0;
pub const SYSCFG: *mut SYSCFG_TypeDef = (1073741824 as uint32_t + 65536 + 0) as *mut SYSCFG_TypeDef;
