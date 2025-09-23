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

#include "rpi3hw.h"

static void enable_af_pins(int clock, uint32_t bitmask)
{
	uint32_t clock_reg;
	int i;

	switch(clock)
	{
	case 0: clock_reg = GPPUDCLK0; break;
	case 1: clock_reg = GPPUDCLK1; break;
	default: return;
	}

	writel(GPPUD, 0);

	for(i = 0; i < 150; i++) nop();

	writel(clock_reg, bitmask);

	for(i = 0; i < 150; i++) nop();

	writel(clock_reg, 0);
}


void uart_init(void)
{
	writel(AUX_ENABLES, 1);			// enable UART peripheral
	writel(AUX_MU_IER_REG, 0);		// disable UART interrupts for config
	writel(AUX_MU_CNTL_REG, 0);		// disable UART RX/TX for config
	writel(AUX_MU_LCR_REG, 3);		// 8 bit mode (bit 1 reserved!)
	writel(AUX_MU_MCR_REG, 0);		// RTS line high
	writel(AUX_MU_IER_REG, 0);		// disable UART interrupts
	writel(AUX_MU_IIR_REG, 0xC6);	// enable and clear FIFOs
	writel(AUX_MU_BAUD_REG, 270);	// 115200 Baud

	uint32_t gpfsel1;

	gpfsel1 = readl(GPFSEL1);
	gpfsel1 &= ~(GPFSEL_PIN_MASK << 12);	// Gpio14
	gpfsel1 |= (GPFSEL_ALT_5		<< 12);	// Alt5: UART_TXD
	gpfsel1 &= ~(GPFSEL_PIN_MASK << 15); // Gpio15
	gpfsel1 |= (GPFSEL_ALT_5		<< 15);	// Alt5: UART_RXD
	writel(GPFSEL1, gpfsel1);

	enable_af_pins(0, BIT(14) | BIT(15));

	// enable UART RX/TX again
	writel(AUX_MU_CNTL_REG,3);
}

