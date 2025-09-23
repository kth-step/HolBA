
.globl _cores123
.globl _hang

.section .text


_cores123:
	sub r2, r2, #1
	mov r3, #0
	cmp r2, r3
	bne _cores23
	// only core 1 continues

	ldr r5, =0x00200000
	mov sp, r5
	bl main_core1
	b _hang


_cores23:
	sub r2, r2, #1
	mov r3, #0
	cmp r2, r3
	bne _cores3
	// only core 2 continues

	ldr r5, =0x00300000
	mov sp, r5
	bl main_core2
	b _hang


_cores3:
	sub r2, r2, #1
	mov r3, #0
	cmp r2, r3
	bne _hang
	// only core 3 continues

	ldr r5, =0x00400000
	mov sp, r5
	bl main_core3
	b _hang



	// an infinite loop
_hang:	wfe
	b _hang


