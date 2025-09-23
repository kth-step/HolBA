
.globl _start

.globl _embexp_entry

.section .text
_start:
	// all four cores are executing from here

	// first, we need to stop all cores except core0
	mrc p15, 0, r2, c0, c0,  5
	and r2, r2, #0xFF
	mov r3, #0
	cmp r2, r3
	bne _cores123
	// only core 0 continues

_reset_core0:
_embexp_entry:
	// TODO: set exception vector base address

	// ... to execute the main c function
	ldr r5, =0x00100000
	mov sp, r5
	bl main
	b _hang


