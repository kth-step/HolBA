/*
 * Author: Aurelio Colosimo, 2017, MIT License
 */

#ifndef _STM32F411X_
#define _STM32F411X_

#include <cpu.h>

/* RCC registers */
#define RCC_CR       reg32(0x40021000)
#define RCC_CFGR     reg32(0x40021004)
#define RCC_CIR      reg32(0x40021008)
#define RCC_APB2RSTR reg32(0x4002100C)
#define RCC_APB1RSTR reg32(0x40021010)
#define RCC_AHBENR   reg32(0x40021014)
#define RCC_APB2ENR  reg32(0x40021018)
#define RCC_APB1ENR  reg32(0x4002101C)
#define RCC_BDCR     reg32(0x40021020)
#define RCC_CSR      reg32(0x40021024)
#define RCC_AHBRSTR  reg32(0x40021028)
#define RCC_CFGR2    reg32(0x4002102C)
#define RCC_CFGR3    reg32(0x40021030)
#define RCC_CR2      reg32(0x40021034)

/* GPIOA registers */
#define R_GPIOA_MODER   reg32(0x48000000)
#define R_GPIOA_OTYPER  reg32(0x48000004)
#define R_GPIOA_OSPEEDR reg32(0x48000008)
#define R_GPIOA_PUPDR   reg32(0x4800000c)
#define R_GPIOA_IDR     reg32(0x48000010)
#define R_GPIOA_ODR     reg32(0x48000014)
#define R_GPIOA_BSRR    reg32(0x48000018)
#define R_GPIOA_LCKR    reg32(0x4800001c)
#define R_GPIOA_AFRL    reg32(0x48000020)
#define R_GPIOA_AFRH    reg32(0x48000024)
#define R_GPIOA_BRR     reg32(0x48000028)

/* USART1 registers */
#define R_USART1_CR1    reg32(0x40013800)
#define R_USART1_CR2    reg32(0x40013804)
#define R_USART1_CR3    reg32(0x40013808)
#define R_USART1_BRR    reg32(0x4001380C)
#define R_USART1_GTPR   reg32(0x40013810)
#define R_USART1_RTOR   reg32(0x40013814)
#define R_USART1_RQR    reg32(0x40013818)
#define R_USART1_ISR    reg32(0x4001381C)
#define R_USART1_ICR    reg32(0x40013820)
#define R_USART1_RDR    reg32(0x40013824)
#define R_USART1_TDR    reg32(0x40013828)

/* Flash interface registers */
#define R_FLASH_ACR     reg32(0x40022000)
#define R_FLASH_KEYR    reg32(0x40022004)
#define R_FLASH_OPTKEYR reg32(0x40022008)
#define R_FLASH_SR      reg32(0x4002200c)
#define R_FLASH_CR      reg32(0x40022010)
#define R_FLASH_OPTCR   reg32(0x40022014)

#endif /* _STM32F411X_ */
