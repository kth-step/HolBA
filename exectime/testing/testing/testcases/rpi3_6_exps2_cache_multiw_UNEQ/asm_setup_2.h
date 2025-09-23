
	// reset the temporary registers to zero
	mov x0, #0
	mov x1, #0


	// x2 = 0x0000000080100d40
	movk x2, #0x0d40, lsl #0
	movk x2, #0x8010, lsl #16
	movk x2, #0x0000, lsl #32
	movk x2, #0x0000, lsl #48


