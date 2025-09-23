/*
 * uart.c
 *
 *  Created on: 11 apr. 2019
 *      Author: Andreas Lindner
 */

#include "LPC11xx.h"
#include <stdint.h>

/*
Bluetooth (HC-06)
--------------
TX&RX
- PIO1_6/RXD/CT32B0_MAT0
- PIO1_7/TXD/CT32B0_MAT1
*/

/*
--------------------------------------------------------------------------------------------
 */

void uart_init()
{
	// enable RXD
    LPC_IOCON->PIO1_6 &= ~(2<<4)|(1<<0);
    LPC_IOCON->PIO1_6 |= (2<<4)|(1<<0);
    LPC_IOCON->PIO1_6 &= ~(0x1F);
    LPC_IOCON->PIO1_6 |= (0x1);

    // enable TXD
    LPC_IOCON->PIO1_7 &=~(2<<4)|(1<<0);
    LPC_IOCON->PIO1_7 |=(2<<4)|(1<<0);

    // enable clock for UART peripheral
    LPC_SYSCON->SYSAHBCLKCTRL |= (1<<12);

    // set up line control, 8 data bits + 1 stop bit
    LPC_UART->LCR = (0x3 << 0);

    // enable hardware FIFO
    LPC_UART->FCR = 0x07;

    // enable RDA interrupt
	//LPC_UART->IER = 1;
	//NVIC_SetPriority(UART_IRQn, 1);
	//NVIC_EnableIRQ(UART_IRQn);

    // enable UART clocking, clock divider setting, 36MHz, baudrate 19200
    LPC_SYSCON->UARTCLKDIV = 36*1000*1000 / 16 / 9600;

}

int uart_write(char c)
{
	if (!(LPC_UART->LSR & 0x20))
		return -1;
	//while (!(LPC_UART->LSR & 0x20));

	LPC_UART->THR = c;
	return 0;
}

int uart_read()
{
	if (!(LPC_UART->LSR & 0x1))
		return -1;

	return LPC_UART->RBR;
}


void uart_putchar(char c) {
	while (uart_write(c));
}

char uart_getchar() {
	int c;
	while ((c = uart_read()) < 0);

	return (char)c;
}



