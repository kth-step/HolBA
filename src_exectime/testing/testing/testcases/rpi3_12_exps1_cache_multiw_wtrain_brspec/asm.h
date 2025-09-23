	ldr x12, [x2]
	cmp x6, x5
	b.eq #0xC
	//add x10,x10,x10
	ldr x11, [x1]
	b #0x8
	nop
