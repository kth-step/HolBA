/*
 * Author: Aurelio Colosimo, 2016
 * Originally modified from kim-os project:
 * https://github.com/colosimo/kim-os
 */

#include <gpio.h>
#include <stm32f411x.h>
#include "lib/printf.h"

#define attr_sect(x) __attribute__((section(x))) \
    __attribute__((aligned(4))) \
    __attribute__((used))

#define STACK_TOP ((void*)(0x20002000))

/* NOTE: The following values are hard-coded defines according to isr_reset
 * code. I'm lazy, so isr_reset is not actually using the defines, but the
 * values below are the result of isr_reset clock settings commands */
#define HSE_FREQ   8000000 /* 8MHz external crystal */
#define PLLMUL           6
#define CPU_FREQ   (HSE_FREQ * PLLMUL)
#define AHB_PRESCALER 1
#define APB_PRESCALER 1
#define HCLCK (CPU_FREQ / AHB_PRESCALER)
#define PCLK (HCLK / APB_PRESCALER)
#define SYSTICKS_FREQ      1000

#define NO_FLASH_LATENCY 1

static uint32_t ticks = 0;

extern unsigned char _sdata_flash;
extern unsigned char _sdata;
extern unsigned char _edata;
extern unsigned char _sbss;
extern unsigned char _ebss;

extern int main();

void uart_init() {
	#ifdef NO_FLASH_LATENCY
		const int no_flash_latency = 1;
	#else
		const int no_flash_latency = 0;
	#endif

	/* Init USART1 on PA9/PA10 */
	gpio_func(IO(PORTA, 9), 1);
	gpio_func(IO(PORTA, 10), 1);
	gpio_mode(IO(PORTA, 9), PULL_NO);
	gpio_mode(IO(PORTA, 10), PULL_NO);

	/*  fPCLK=48MHz, br=115.2KBps, BRR=0x1A1, see table 104 pag. 704 */
	wr32(R_USART1_BRR, 0x1a1 / (no_flash_latency ? 6 : 1));
	or32(R_USART1_CR1, BIT3 | BIT2 | BIT0);

	// avoid receiving some wrong byte first, there must be a better way to fix this though
	for (int i = 0; i < 100; i++) {
		rd32(R_USART1_ISR);
		rd32(R_USART1_RDR);
	}
}

int uart_write(char c)
{
	/* Wait for data sent (TDR becomes empty */
	if (!(rd32(R_USART1_ISR) & BIT7))
		return -1;

	/* Write byte to tx register (TDR) */
	wr32(R_USART1_TDR, c);
	return 0;
}

int uart_read()
{
	/* wait for data to arrive */
	if (!(rd32(R_USART1_ISR) & BIT5))
		return -1;

	/* read byte from rx register (RDR) */
	return rd32(R_USART1_RDR)&0xFF;
}

void uart_putchar(char c) {
	while (uart_write(c));
}

char uart_getchar() {
	int c;
	while ((c = uart_read()) < 0);

	return (char)c;
}

static void isr_reset(void)
{
	unsigned char *src, *dest;

	/* Load data to ram */
	src = &_sdata_flash;
	dest = &_sdata;
	while (dest != &_edata)
		*dest++ = *src++;

	/* Set bss section to 0 */
	dest = &_sbss;
	while (dest != &_ebss)
		*dest++ = 0;

	/* Enable HSE (8MHz external oscillator) */
	or32(RCC_CR, BIT16);
	while (!(rd32(RCC_CR) & BIT17));

	/* PLLMUL=6 f_PLL=48MHz */
	and32(RCC_CFGR, ~((0b1111 << 18) | (0b11 << 15) | BIT17));
	or32(RCC_CFGR, (0b0100 << 18) | (0b11 << 15));
	or32(RCC_CR, BIT24);
	while (!(rd32(RCC_CR) & BIT25));

	/* Configure flash, LATENCY=001 */
	while(rd32(R_FLASH_SR) & BIT0);
	wr32(R_FLASH_ACR, 0b001);

	#ifdef NO_FLASH_LATENCY
		wr32(R_FLASH_ACR, 0b000);
	#else
		/* Use PLL as system clock */
		or32(RCC_CFGR, 0b10);
		while (((rd32(RCC_CFGR) >> 2) & 0x3) != 0b10);
	#endif

	/* Enable clock on used AHB and APB peripherals */
	or32(RCC_APB2ENR, BIT14); /* USART1 */
	or32(RCC_AHBENR, BIT17); /* GPIOA */

	/* Init systicks */
	ticks = 0;
	wr32(R_SYST_RVR, HCLCK / SYSTICKS_FREQ);
	wr32(R_SYST_CVR, 0);
	wr32(R_SYST_CSR, BIT0 | BIT1 | BIT2);

	uart_init();

	main();
}

static void isr_none(void)
{
	printf(__func__);
	while(1);
}

static void isr_nmi(void)
{
	printf(__func__);
	while(1);
}

static void isr_hf(void)
{
	printf(__func__);
	while(1);
}

static void isr_systick(void)
{
	ticks++;
}

uint32_t systicks(void)
{
	return ticks;
}

static const void *attr_sect("isrv_sys") _isrv_sys[] = {
	/* Cortex-M0 system interrupts */
	STACK_TOP,	/* Stack top */
	isr_reset,	/* Reset */
	isr_nmi,	/* NMI */
	isr_hf,	/* Hard Fault */
	0,			/* Reserved */
	0,			/* Reserved */
	0,			/* Reserved */
	0,			/* Reserved */
	0,			/* Reserved */
	0,			/* Reserved */
	0,			/* Reserved */
	isr_none,	/* SVCall */
	0,			/* Reserved */
	0,			/* Reserved */
	isr_none,	/* PendSV */
	isr_systick,	/* SysTick */
};

static const void *attr_sect("isrv_irq") _isrv_irq[] = {
	/* Peripheral interrupts */
	isr_none, /* WWDG */
	isr_none, /* PVD_VDDIO2 */
	isr_none, /* RTC */
	isr_none, /* FLASH */
	isr_none, /* RCC_CRS */
	isr_none, /* EXTI0_1 */
	isr_none, /* EXTI2_3 */
	isr_none, /* EXTI4_15 */
	isr_none, /* TSC */
	isr_none, /* DMA_CH1 */
	isr_none, /* DMA_CH2_3, DMA2_CH1_2 */
	isr_none, /* DMA_CH4_5_6_7, DMA2_CH3_4_5  */
	isr_none, /* ADC_COMP */
	isr_none, /* TIM1_BRK_UP_TRG_COM */
	isr_none, /* TIM1_CC */
	isr_none, /* TIM2 */
	isr_none, /* TIM3 */
	isr_none, /* TIM6_DAC */
	isr_none,  /* TIM7 */
	isr_none, /* TIM14 */
	isr_none, /* TIM15 */
	isr_none, /* TIM16 */
	isr_none, /* TIM17 */
	isr_none, /* I2C1 */
	isr_none, /* I2C2 */
	isr_none, /* SPI1 */
	isr_none, /* SPI2 */
	isr_none, /* USART1 */
	isr_none, /* USART2 */
	isr_none, /* USART_3_4_5_6_7_8 */
	isr_none, /* CEC_CAN */
	isr_none, /* USB */
};
