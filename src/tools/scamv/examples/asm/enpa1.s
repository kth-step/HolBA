
	cmp x2, x3
	b.lo __scamv_lbl
	add x1, x2, x3
__scamv_lbl:
	ldr x2, [x1]
