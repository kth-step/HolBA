
.globl _start

.globl _embexp_entry

.section .text
_start:
	// all four cores are executing from here

	// first, we need to stop all cores except core0
	mrs x2, MPIDR_EL1
	and x2, x2, #0xFF
	cbnz x2, _cores123
	// only core 0 continues

	// then, core0 can move on to call the function setting the status LED, and ...
	mov w0, #1
	bl _set_led

_reset_core0:
_embexp_entry:
	// set exception vector base address
	adr x0, vectors
	msr vbar_el3, x0
	msr vbar_el2, x0
	msr vbar_el1, x0
	// ... to execute the main c function
	ldr x5, =__stack_memory_top
	mov sp, x5
	bl main
	b _hang


