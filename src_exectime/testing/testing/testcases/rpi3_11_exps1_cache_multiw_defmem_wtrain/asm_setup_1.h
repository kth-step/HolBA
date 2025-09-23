	// x0 = 0x0000000080100000
	movk x0, #0x0000, lsl #0
	movk x0, #0x8010, lsl #16
	movk x0, #0x0000, lsl #32
	movk x0, #0x0000, lsl #48

	// for magic default memory value comparison
	//mov x10, #0x0
	mov x20, #0x0

	// create different addresses in terms of cache set index
	add x11, x0 , #(3* 64)
	add x12, x11, #(2* 64)

