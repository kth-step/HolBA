
	// x0 = 0x0000000080100000
	movk x0, #0x0000, lsl #0
	movk x0, #0x8010, lsl #16
	movk x0, #0x0000, lsl #32
	movk x0, #0x0000, lsl #48

	add x1, x0, #64
	add x2, x1, #64


	mov x5, #0x08
	mov x6, #0x18


