#define __IO

typedef unsigned int uint32_t;

typedef struct
{
  __IO uint32_t MEMRMP;      /*!< SYSCFG memory remap register,                      Address offset: 0x00      */
  __IO uint32_t CFGR1;       /*!< SYSCFG configuration register 1,                   Address offset: 0x04      */
  __IO uint32_t EXTICR[4];   /*!< SYSCFG external interrupt configuration registers, Address offset: 0x08-0x14 */
  __IO uint32_t SCSR;        /*!< SYSCFG SRAM2 control and status register,          Address offset: 0x18      */
  __IO uint32_t CFGR2;       /*!< SYSCFG configuration register 2,                   Address offset: 0x1C      */
  __IO uint32_t SWPR;        /*!< SYSCFG SRAM2 write protection register,            Address offset: 0x20      */
  __IO uint32_t SKR;         /*!< SYSCFG SRAM2 key register,                         Address offset: 0x24      */
  __IO uint32_t SWPR2;       /*!< SYSCFG SRAM2 write protection register 2,          Address offset: 0x28      */
} SYSCFG_TypeDef;

#define PERIPH_BASE           ((uint32_t)0x40000000U) /*!< Peripheral base address */

#define APB2PERIPH_BASE       (PERIPH_BASE + 0x00010000U)

#define SYSCFG_BASE           (APB2PERIPH_BASE + 0x0000U)

#define SYSCFG ((SYSCFG_TypeDef *) SYSCFG_BASE)
