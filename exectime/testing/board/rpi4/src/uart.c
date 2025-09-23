#include "rpi4hw.h"
#include "uart.h"

void uart_init()
{
  // disable first
  writel(UART_UARTLCR_H, 0);
  writel(UART_UARTCR, 0);

  // set baudrate
  writel(UART_UARTIBRD, 26);
  writel(UART_UARTFBRD, 3);

  // enable lines and uart
  writel(UART_UARTLCR_H, (3 << 5) | (1 << 4));
  writel(UART_UARTCR, (1 << 9) | (1 << 8) | (1 << 0));
}

void uart_putchar(char c)
{
  while (readl(UART_UARTFR) & (1 << 5));
  writel(UART_UARTDR, c);
}

char uart_getchar()
{
  while (readl(UART_UARTFR) & (1 << 4));

  uint32_t data = readl(UART_UARTDR);
  readl(UART_UARTRSR);

  return (char)data;
}

