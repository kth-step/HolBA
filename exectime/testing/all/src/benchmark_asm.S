#ifdef __BENCHMARK_MODE

//.syntax unified

.globl _benchmark_timer_reset
.globl _benchmark_timer_measure
.globl _benchmark_helper_wait_1ms

.globl _imu_handler_pid_entry_dummy

.section .text
_benchmark_timer_reset:
	dmb
	dsb
	isb
	// reset timer here
	mov r1, #0x5
	ldr r0, =0xE000E010  // SYST_CSR
	str r1, [r0]
	ldr r1, =0xFFFFFF
	ldr r0, =0xE000E014  // SYST_RVR
	str r1, [r0]
	ldr r0, =0xE000E018  // SYST_CVR
	str r1, [r0]
	dmb
	dsb
	isb
	bx lr



_benchmark_timer_measure:
	dmb
	dsb
	isb
	// measure time here, and store it in r0
	// (what's the impact of the load and store on the measurement? is it always the same constant value?)
	// (we should keep them but do we need all the barriers?)
	ldr r0, =0xE000E018  // SYST_CVR
	ldr r1, [r0]
	ldr r0, =0xE000E014  // SYST_RVR
	ldr r0, [r0]
	sub r0, r0, r1
	// TODO: check countflag in status register, set r0 to 0xFFFFFFFF in this case
	ldr r1, =0xE000E010  // SYST_CSR
	ldr r3, [r1]
	lsr r2, r3, #16   // The COUNTFLAG corresponds to the bit 16 of the SYST_CVR register
	//and r2, r2, #0x00000001
	cmp r2, #0
	beq _NoOverflow
	ldr r0, =0xFFFFFFFF
	_NoOverflow:
	dmb
	dsb
	isb
	bx lr

_benchmark_helper_wait_1ms:
	ldr r1, =1000
_benchmark_helper_wait_1ms_loop:
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	sub r1, r1, #1
	cmp r1, #0
	bne _benchmark_helper_wait_1ms_loop
	bx lr

_imu_handler_pid_entry_dummy:
	bx lr

#endif

