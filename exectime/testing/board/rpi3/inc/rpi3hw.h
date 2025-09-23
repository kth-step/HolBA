/*
 * Derived from code:
 * 
 * https://github.com/swarren/rpi-3-aarch64-demo
 * Copyright (C) 2012 Vikram Narayananan <vikram186@gmail.com>
 * (C) Copyright 2012-2016 Stephen Warren
 * Copyright (C) 1996-2000 Russell King
 *
 * SPDX-License-Identifier:	GPL-2.0
 *
 * https://github.com/dwelch67/raspberrypi/tree/master/armjtag
 * Copyright (c) 2012 David Welch dwelch@dwelch.com
 */

#ifndef _RPI3HW_H
#define _RPI3HW_H

#include <stdint.h>

#define BIT(x)	(1U << (x))

#define PERI_BASE				(0x3F000000)

#define MU_BASE					(PERI_BASE + 0x00215040)
#define MU_LSR_TX_NOT_FULL		(BIT(5))
#define MU_LSR_RX_READY			(BIT(0))

#define AUX_ENABLES				(PERI_BASE + 0x00215004)
#define AUX_MU_IO_REG			(PERI_BASE + 0x00215040)
#define AUX_MU_IER_REG			(PERI_BASE + 0x00215044)
#define AUX_MU_IIR_REG			(PERI_BASE + 0x00215048)
#define AUX_MU_LCR_REG			(PERI_BASE + 0x0021504C)
#define AUX_MU_MCR_REG			(PERI_BASE + 0x00215050)
#define AUX_MU_LSR_REG			(PERI_BASE + 0x00215054)
#define AUX_MU_MSR_REG			(PERI_BASE + 0x00215058)
#define AUX_MU_SCRATCH			(PERI_BASE + 0x0021505C)
#define AUX_MU_CNTL_REG			(PERI_BASE + 0x00215060)
#define AUX_MU_STAT_REG			(PERI_BASE + 0x00215064)
#define AUX_MU_BAUD_REG			(PERI_BASE + 0x00215068)

#define GPFSEL0					(PERI_BASE + 0x00200000)
#define GPFSEL1					(PERI_BASE + 0x00200004)
#define GPFSEL2					(PERI_BASE + 0x00200008)
#define GPSET0					(PERI_BASE + 0x0020001C)
#define GPCLR0					(PERI_BASE + 0x00200028)
#define GPPUD					(PERI_BASE + 0x00200094)
#define GPPUDCLK0				(PERI_BASE + 0x00200098)
#define GPPUDCLK1				(PERI_BASE + 0x0020009C)

#define GPFSEL_PIN_MASK			(7U)//(BIT(2) | BIT(1) | BIT(0))
#define GPFSEL_ALT_4			(3U)//(BIT(1) | BIT(0))
#define GPFSEL_ALT_5			(2U)//(BIT(1))

#define __arch_getl(a)		(*(volatile unsigned int *)(a))
#define __arch_putl(v,a)	(*(volatile unsigned int *)(a) = (v))

#define dmb()				__asm__ __volatile__ ("dmb st" : : : "memory")
#define nop()				__asm__ __volatile__ ("nop")
#define __iormb()			dmb()
#define __iowmb()			dmb()

struct bcm283x_mu_regs {
	uint32_t io;
	uint32_t iir;
	uint32_t ier;
	uint32_t lcr;
	uint32_t mcr;
	uint32_t lsr;
	uint32_t msr;
	uint32_t scratch;
	uint32_t cntl;
	uint32_t stat;
	uint32_t baud;
};

static inline uint32_t readl(uint64_t addr)
{
	uint32_t value = __arch_getl(addr);
	__iormb();
	return value;
}


static inline void writel(uint64_t addr, uint32_t value)
{
	__arch_putl(value, addr);
	__iowmb();
}

#endif
