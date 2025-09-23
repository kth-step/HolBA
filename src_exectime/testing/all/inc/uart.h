#ifndef _UART_H
#define _UART_H

void uart_init();

void uart_putchar(char c);
char uart_getchar();

// from uart_gen.c
void uart_print_string(char* str);
void uart_echoloop();

#endif
