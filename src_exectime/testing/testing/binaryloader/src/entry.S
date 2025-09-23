
.section .text
.globl _start
_start:

	// x0 = 0x0000000080100000
	movk x0, #0x0000, lsl #0
	movk x0, #0x8010, lsl #16
	movk x0, #0x0000, lsl #32
	movk x0, #0x0000, lsl #48

	add x1, x0, #0x00
	ldrb w2, [x1]
	b hang

	// x0 = 0x0000000080100000
	movk x0, #0x0000, lsl #0
	movk x0, #0x8010, lsl #16
	movk x0, #0x0000, lsl #32
	movk x0, #0x0000, lsl #48

	add x1, x0, #0xF0
	ldrb w2, [x1]
	b hang

hang:
	b hang

