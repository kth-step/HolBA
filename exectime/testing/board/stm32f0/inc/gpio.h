/*
 * Author: Aurelio Colosimo, 2017, MIT License
 */

#ifndef _GPIO_H_
#define _GPIO_H_

#include <stm32f411x.h>
#include <basic.h>

#define PORTA 0
#define PORTB 1
#define PORTC 2
#define PORTD 3
#define PORTE 4
#define PORTH 7

#define IO(port, pin) (((port) << 8) | (pin))
#define PORT(io) ((io) >> 8)
#define PIN(io) ((io) & 0xff)

#define GPIOx_MODER(x) (R_GPIOA_MODER + (0x400 * PORT(x)) / 4)
#define GPIOx_OTYPER(x) (R_GPIOA_OTYPER + (0x400 * PORT(x)) / 4)
#define GPIOx_IDR(x)   (R_GPIOA_IDR   + (0x400 * PORT(x)) / 4)
#define GPIOx_BSRR(x)  (R_GPIOA_BSRR  + (0x400 * PORT(x)) / 4)
#define GPIOx_AFRL(x)  (R_GPIOA_AFRL  + (0x400 * PORT(x)) / 4)
#define GPIOx_AFRH(x)  (R_GPIOA_AFRH  + (0x400 * PORT(x)) / 4)
#define GPIOx_AFR(x)   (PIN(x) < 8 ? GPIOx_AFRL(x) : GPIOx_AFRH(x))
#define GPIOx_PUPDR(x) (R_GPIOA_PUPDR + (0x400 * PORT(x)) / 4)

#define PULL_UP   0b01
#define PULL_NO   0b00
#define PULL_DOWN 0b10

#define PINSEL(io) (PINSEL0 + 2 * PORT(io) + PIN(io) / 16)
#define PINMODE(io) (PINMODE0 + 2 * PORT(io) + PIN(io) / 16)

static inline void gpio_dir(u16 io, int out)
{
	volatile u32 *reg = GPIOx_MODER(io);
	and32(reg, ~(0b11 << (2 * PIN(io))));
	if (out)
		or32(reg, (0b01 << (2 * PIN(io))));
}

static inline int gpio_rd(u16 io)
{
	return (rd32(GPIOx_IDR(io)) >> PIN(io)) & 0x1;
}

static inline void gpio_wr(u16 io, int v)
{
	wr32(GPIOx_BSRR(io), 1 << (PIN(io) + (v ? 0 : 16)));
}

static inline void gpio_func(u16 io, u8 f)
{
	volatile u32 *reg_afr;
	volatile u32 *reg_moder;
	reg_afr = GPIOx_AFR(io);
	reg_moder = GPIOx_MODER(io);
	and32(reg_afr, ~(0b1111 << (4 * (PIN(io) % 8))));
	and32(reg_moder, ~(0b11 << (2 * PIN(io))));
	or32(reg_moder, (0b10 << (2 * PIN(io))));
	or32(reg_afr, ((u32)f & 0b1111) << (4 * (PIN(io) % 8)));
}

static inline void gpio_mode(u16 io, u8 f)
{
	volatile u32 *reg = GPIOx_PUPDR(io);
	and32(reg, ~(3 << (2 * (PIN(io) % 16))));
	or32(reg, ((u32)f) << (2 * (PIN(io) % 16)));
}

static inline void gpio_odrain(u16 io, int odrain)
{
	volatile u32 *reg = GPIOx_OTYPER(io);
	and32(reg, ~(1 << PIN(io)));
	if (odrain)
		or32(reg, (1 << PIN(io)));
}

#endif /* _GPIO_H_ */
