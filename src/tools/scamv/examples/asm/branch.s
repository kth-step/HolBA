	mov	x3, #0x3
	add	x1, x1, x0
	ldr	x0, [x4]
	cmp	x1, x3
	b.hi	#0xC
	ldr	x0, [x4]
	add	x2, x2, #0x1
	
	mov	x0, x2
