/*
 * Derived from code:
 * 
 * https://github.com/dwelch67/sifive_samples/blob/master/hifive1/uart03/notmain.c
 */

#include "arty_a7_100t__fe310_hw.h"
#include <stdint.h>

void uart_init()
{
// 32M /  57600 = 556
#define DIVVAL 556

    uint32_t temp;

    temp  = GET32(GPIO_IOF_SEL);
    temp &= ~(1<<16); //UART0_RX
    temp &= ~(1<<17); //UART0_TX
    PUT32(GPIO_IOF_SEL, temp);

    temp  = GET32(GPIO_IOF_EN);
    temp |= 1<<16; //UART0_RX
    temp |= 1<<17; //UART0_TX
    PUT32(GPIO_IOF_EN, temp);

    PUT32(UART0_DIV   , DIVVAL-1);
    PUT32(UART0_TXCTRL, 0x00000003);
    PUT32(UART0_RXCTRL, 0x00000001);
}

void uart_putchar(char c) {
    while((GET32(UART0_TXDATA) & 0x80000000) != 0);
    PUT32(UART0_TXDATA, (uint32_t)c);
}

char uart_getchar() {
    uint32_t data;
    while(((data = GET32(UART0_RXDATA)) & 0x80000000) != 0);
    return (char)(data & 0xFF);
}


