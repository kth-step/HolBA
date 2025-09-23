#include "uart.h"

void uart_print_string(char* str)
{
  while(*str) {
    uart_putchar(*str);
    str++;
  }
}

void uart_echoloop()
{
  while(1) {
    uart_putchar(uart_getchar());
  }
}

