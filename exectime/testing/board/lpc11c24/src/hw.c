/*
 * hw.c
 *
 *  Created on: 12 apr. 2019
 *      Author: Andreas Lindner
 */


#include "LPC11xx.h"

/*
 NXP LPCxxxx ISP
	ISP pin: P0.1 - for LPC11xx
	GND the ISP pin,
	assert RST,
	then remove the GND to ISP pin.
 */


/*
--------------------------------------------------------------------------------------------
 */

void hw_clock_init()
{
	// 1. see CMSISv2.00/src/system_LPC11xx.c
	// 1. a) M = 4		P = 2
	// 1. b) FCCO = 192MHz
	// 1. c) range of FCCO: 156 to 320 MHz, yes it is in the allowed range
	// 1. d) 48MHz

	// set CLKOUT source to main clock
	LPC_SYSCON->CLKOUTCLKSEL	= 0x3;		// set clock out to main clock
	LPC_SYSCON->CLKOUTDIV		= 0x1;		// set clock output divider to 1:1
	LPC_SYSCON->CLKOUTUEN		= 0x0;		// update output mux
	LPC_SYSCON->CLKOUTUEN		= 0x1;		// needs to be toggled
	while (!(LPC_SYSCON->CLKOUTUEN & 0x01));
	//LPC_IOCON->PIO0_1			= 0x1;		// set pin to function as CLKOUT

	// 2. set main clock to PLLIN
	LPC_SYSCON->MAINCLKSEL		= 0x1;		// select PLL input for main clock
	LPC_SYSCON->MAINCLKUEN		= 0x0;		// update main clock select mux
	LPC_SYSCON->MAINCLKUEN		= 0x1;		// needs to be toggled

	// 2.a) see UserManual p.24 and oscillator setup: system oscillator is select in PLLINMUX, 12MHz crystal
	// 2.b) SYSOSCCTRL, no bypass/no external clock source - 12 MHz crystal
	// 2.c) 12MHz
	while (!(LPC_SYSCON->MAINCLKUEN & 0x01));

	// 3.a) M = 3		P = 4		FCCO = 288MHz
	// 3.b) 36MHz
	LPC_SYSCON->PDRUNCFG		|= (1 << 7);
	LPC_SYSCON->SYSPLLCTRL		= (2 << 0) | (2 << 4);
	LPC_SYSCON->PDRUNCFG		&= ~(1 << 7);
	while (!(LPC_SYSCON->SYSPLLSTAT & 0x01));
	LPC_SYSCON->MAINCLKSEL		= 0x3;
	LPC_SYSCON->MAINCLKUEN		= 0x0;
	LPC_SYSCON->MAINCLKUEN		= 0x1;
	while (!(LPC_SYSCON->MAINCLKUEN & 0x01));

	// 4.a) SYSAHBCLKDIV
	// 4.b)
	LPC_SYSCON->SYSAHBCLKDIV	= 3;
}



/*
--------------------------------------------------------------------------------------------
 */


#include <stdint.h>

void hw_gpio_init() {
	  /* Enable AHB clock to the GPIO domain. */
	  LPC_SYSCON->SYSAHBCLKCTRL |= (1<<6);
}

static LPC_GPIO_TypeDef* getGPIO(uint32_t portNum)
{
	LPC_GPIO_TypeDef* LPC_GPIO_cur;

	switch (portNum)
	{
	case 0:
		LPC_GPIO_cur = LPC_GPIO0;
		break;
	case 1:
		LPC_GPIO_cur = LPC_GPIO1;
		break;
	case 2:
		LPC_GPIO_cur = LPC_GPIO2;
		break;
	case 3:
		LPC_GPIO_cur = LPC_GPIO3;
		break;
	default:
		while (1);
	}

	return LPC_GPIO_cur;
}

void hw_gpio_set( uint32_t portNum, uint32_t bitPosi, uint32_t bitVal )
{
	getGPIO(portNum)->MASKED_ACCESS[(1<<bitPosi)] = (bitVal<<bitPosi);
}

uint32_t hw_gpio_get( uint32_t portNum, uint32_t bitPosi )
{
	return (getGPIO(portNum)->MASKED_ACCESS[(1<<bitPosi)]>>bitPosi) & 0x1;
}

void hw_gpio_set_dir( uint32_t portNum, uint32_t bitPosi, uint32_t dir )
{
  if(dir)
	  getGPIO(portNum)->DIR |= 1<<bitPosi;
  else
	  getGPIO(portNum)->DIR &= ~(1<<bitPosi);
}


