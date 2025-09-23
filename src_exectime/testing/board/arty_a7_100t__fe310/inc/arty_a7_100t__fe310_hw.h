/*
 * Derived from code:
 * 
 * https://github.com/dwelch67/sifive_samples/blob/master/hifive1/uart03/notmain.c
 */

#ifndef _ARTY_A7_100T__FE310_HW_H
#define _ARTY_A7_100T__FE310_HW_H

#include <stdint.h>

void PUT32( unsigned int, unsigned int);
unsigned int GET32 ( unsigned int );
void  dummy ( unsigned int );
unsigned int MCYCLE ( void );
unsigned int AMOSWAP ( unsigned int, unsigned int);

#define GPIOBASE 0x10012000
#define GPIO_VALUE          (GPIOBASE+0x00)
#define GPIO_INPUT_EN       (GPIOBASE+0x04)
#define GPIO_OUTPUT_EN      (GPIOBASE+0x08)
#define GPIO_PORT           (GPIOBASE+0x0C)
#define GPIO_PUE            (GPIOBASE+0x10)
#define GPIO_OUT_XOR        (GPIOBASE+0x40)
#define GPIO_IOF_EN         (GPIOBASE+0x38)
#define GPIO_IOF_SEL        (GPIOBASE+0x3C)

#define UART0BASE       0x10013000
#define UART0_TXDATA    (UART0BASE+0x00)
#define UART0_RXDATA    (UART0BASE+0x04)
#define UART0_TXCTRL    (UART0BASE+0x08)
#define UART0_RXCTRL    (UART0BASE+0x0C)
#define UART0_IE        (UART0BASE+0x10)
#define UART0_IP        (UART0BASE+0x14)
#define UART0_DIV       (UART0BASE+0x18)

#endif // _ARTY_A7_100T__FE310_HW_H
