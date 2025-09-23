/*
===============================================================================
 Name        : main.c
 Author      : Andreas Lindner
 Version     :
 Copyright   : $(copyright)
 Description : main definition
===============================================================================
*/

#include "LPC11xx.h"

// ============================================================================
void hw_clock_init();
void hw_gpio_init();

void ui_set_led(int i, char on);
void ui_init();

void uart_init();

// returns -1 if the device is busy
int uart_write(char c);
int uart_read();
// ============================================================================

void uart_send(char* str) {
    while (*str) {
        while(uart_write(*str));
        str++;
    }
}

int main();

int main_entry(void) {
    hw_clock_init();
    hw_gpio_init();

    // configure flash access time (careful with changes to this line, has to be in accordance with clock speed setting!)
    LPC_FLASHCTRL->FLASHCFG = (LPC_FLASHCTRL->FLASHCFG & (~0x3)) + 0;

    ui_init();
    char on = 1;
    ui_set_led(0, on);
    ui_set_led(1, on);

/*
    uart_init();
    uart_send("\r\n");
    uart_send("hello!!!\r\n");

    volatile int i = 3;

    while(1) {
        int c;
        i = i + 1;
        if ((c = uart_read()) >= 0)
            while (uart_write((char)c));
    }
*/

    return main();
}
