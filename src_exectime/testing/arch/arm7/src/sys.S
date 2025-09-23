
.section .text
.align 4

.globl get_SCR

get_SCR:
	mrc	p15, 0, r0, c1, c1, 0
	mov	pc, lr

