
scamv_entry:
	cmp x2, x3
	b.lo lb
	add x1, x2, x3
lb:
	ldr x2, [x1]
