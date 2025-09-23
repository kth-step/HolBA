	// get default memory value
	ldrb w10, [x0, #0]

	// create offset together with x1 (for different cache set index with input 1 and 2)
	add x11, x10, x1
	mov x12, #64
	mul x11, x11, x12

	// access the memory
	ldr x13, [x0, x11]

