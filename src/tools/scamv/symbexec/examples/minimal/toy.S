.globl _start

_start:
	cmp x2, x3 
	bgt l1
	b l2
l1: 	
	add x1, x2, x3
l2:	
	ldr x2, [x0]
