
scamv_entry:
	b.eq l2
	mul x1, x2, x3
l2:
	ldr x2, [x1, #8]
