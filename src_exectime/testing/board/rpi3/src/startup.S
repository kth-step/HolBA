
.globl _cores123
.globl _hang

.section .text


_cores123:
	sub x2, x2, #1
	cbnz x2, _cores23
	// only core 1 continues

	ldr x5, =0x00200000
	mov sp, x5
	bl main_core1
	b _hang


_cores23:
	sub x2, x2, #1
	cbnz x2, _cores3
	// only core 2 continues

	ldr x5, =0x00300000
	mov sp, x5
	bl main_core2
	b _hang


_cores3:
	sub x2, x2, #1
	cbnz x2, _hang
	// only core 3 continues

	ldr x5, =0x00400000
	mov sp, x5
	bl main_core3
	b _hang



	// an infinite loop
_hang:	wfe
	b _hang


