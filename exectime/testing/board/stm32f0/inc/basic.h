/*
 * Author: Aurelio Colosimo, 2016
 *
 * This file is part of kim-os project: https://github.com/colosimo/kim-os
 * According to kim-os license, you can do whatever you want with it,
 * as long as you retain this notice.
 */

#ifndef _BASIC_H_
#define _BASIC_H_

#include <intdefs.h>

/* Useful BITx definition, for bitmask computation */
#define BIT0 (1 << 0)
#define BIT1 (1 << 1)
#define BIT2 (1 << 2)
#define BIT3 (1 << 3)
#define BIT4 (1 << 4)
#define BIT5 (1 << 5)
#define BIT6 (1 << 6)
#define BIT7 (1 << 7)
#define BIT8 (1 << 8)
#define BIT9 (1 << 9)
#define BIT10 (1 << 10)
#define BIT11 (1 << 11)
#define BIT12 (1 << 12)
#define BIT13 (1 << 13)
#define BIT14 (1 << 14)
#define BIT15 ((u16)(1 << 15))
#define BIT16 (1 << 16)
#define BIT17 (1 << 17)
#define BIT18 (1 << 18)
#define BIT19 (1 << 19)
#define BIT20 (1 << 20)
#define BIT21 (1 << 21)
#define BIT22 (1 << 22)
#define BIT23 (1 << 23)
#define BIT24 (1 << 24)
#define BIT25 (1 << 25)
#define BIT26 (1 << 26)
#define BIT27 (1 << 27)
#define BIT28 (1 << 28)
#define BIT29 (1 << 29)
#define BIT30 (1 << 30)
#define BIT31 ((u32)(1 << 31))

/* 32 bits registers */
static inline void wr32(volatile u32 *reg, u32 val) {*reg = val;}
static inline u32 rd32(volatile u32 *reg) {return *reg;}
static inline void or32(volatile u32 *reg, u32 val) {*reg |= val;}
static inline void and32(volatile u32 *reg, u32 val) {*reg &= val;}
static inline void clr32(volatile u32 *r, int nbit) {and32(r, ~(1 << nbit));}
static inline void set32(volatile u32 *reg, int nbit) {or32(reg, 1 << nbit);}

/* 16 bits registers */
static inline void wr16(volatile u16 *reg, u16 val) {*reg = val;}
static inline u16 rd16(volatile u16 *reg) {return *reg;}
static inline void or16(volatile u16 *reg, u16 val) {*reg |= val;}
static inline void and16(volatile u16 *reg, u16 val) {*reg &= val;}
static inline void clr16(volatile u16 *reg, int nbit) {and16(reg, ~(1 << nbit));}
static inline void set16(volatile u16 *reg, int nbit) {or16(reg, 1 << nbit);}

/* 8 bits registers */
static inline void wr8(volatile u8 *reg, u8 val) {*reg = val;}
static inline u8 rd8(volatile u8 *reg) {return *reg;}
static inline void or8(volatile u8 *reg, u8 val) {*reg |= val;}
static inline void and8(volatile u8 *reg, u8 val) {*reg &= val;}
static inline void clr8(volatile u8 *reg, int nbit) {and8(reg, ~(1 << nbit));}
static inline void set8(volatile u8 *reg, int nbit) {or8(reg, 1 << nbit);}

uint32_t systicks(void);

#endif /* _BASIC_H_ */
