#include "config.h"

#ifdef RUN_TIME

#if !defined(__has_include)
#  error "need __has_include"
#endif

#if (!__has_include("experiment/asm.h")) || (!__has_include("experiment/asm_setup_1.h"))
#  error "need at least asm code to run and asm code to setup state 1"
#endif

.globl _time_run

// TODO: have _scamv_run not as argument for code directly, but a state index instead
// followup on the TODO before: define possible index range based on h files found ("asm_setup_xyz.h")
.globl _time_run1
#if __has_include("experiment/asm_setup_2.h")
.globl _time_run2
#endif

.section .experiment_code
scamv_entry:
.include "experiment/asm.h"
	ldr r0, =scamv_exit
	add r0, r0, #1
	bx r0


.section .data
.align 3
_sp_store:
	.quad 0
.align 3
_scamv_ret_store:
	.quad 0
.align 3
_scamv_timeafter_store:
	.quad 0

.section .text

_time_run1:
	ldr r0, =_scamv_ret_store
	mov r1, r14
	str r1, [r0]
	ldr r0, =scamv_entry
	add r0, r0, #1
	mov r14, r0
	mov r0,  #0
	mov r1,  #0
.include "experiment/asm_setup_1.h"
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
	bx r14

#if __has_include("experiment/asm_setup_2.h")
_time_run2:
	ldr r0, =_scamv_ret_store
	mov r1, r14
	str r1, [r0]
	ldr r0, =scamv_entry
	add r0, r0, #1
	mov r14, r0
	mov r0,  #0
	mov r1,  #0
.include "experiment/asm_setup_2.h"
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
	bx r14
#endif

scamv_exit:
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
	ldr r1, =_scamv_timeafter_store
	str r0, [r1]
	ldr r0, =_scamv_ret_store
	ldr r1, [r0]
	mov r14, r1
	bx lr


_time_run:
// save registers on stack
	sub sp, sp, #(8 * 40)
	str r0,  [sp, #(8 *  0)] // _scamv_run
	str r1,  [sp, #(8 *  1)]
	str r2,  [sp, #(8 *  2)]
	str r3,  [sp, #(8 *  3)]
	str r4,  [sp, #(8 *  4)]
	str r5,  [sp, #(8 *  5)]
	str r6,  [sp, #(8 *  6)]
	str r7,  [sp, #(8 *  7)]

	mov r0,  r8
	mov r1,  r9
	mov r2,  r10
	mov r3,  r11
	mov r4,  r12
	mov r5,  r13 // SP
	mov r6,  r14 // LR

	str r0,  [sp, #(8 *  8)]
	str r1,  [sp, #(8 *  9)]
	str r2,  [sp, #(8 * 10)]
	str r3,  [sp, #(8 * 11)]
	str r4,  [sp, #(8 * 12)]
	str r5,  [sp, #(8 * 13)] // SP
	str r6,  [sp, #(8 * 14)] // LR

// store SP register
	ldr r0, =_sp_store
	mov r1, sp
	str r1, [r0]

// =======================================================
// context save finished
// =======================================================

// clean experiment memory
	bl _clean_experiment_memory
// move _scamv_run to r14 (LR)
	ldr r1, [sp, #(8 *  0)]
	add r1, r1, #1
	mov r14, r1
// create defined processor state
	mov r0,  #0
	mov r1,  #0
	mov r2,  #0
	mov r3,  #0
	mov r4,  #0
	mov r5,  #0
	mov r6,  #0
	mov r7,  #0
	mov r8,  r0
	mov r9,  r0
	mov r10, r0
	mov r11, r0
	mov r12, r0
	mov r13, r0

// run the experiment code
	blx r14

// =======================================================
// context restore starts
// =======================================================

// restore SP register
	ldr r0, =_sp_store
	ldr r1, [r0]
	mov sp, r1

// restore registers from stack
	ldr r0,  [sp, #(8 *  8)]
	ldr r1,  [sp, #(8 *  9)]
	ldr r2,  [sp, #(8 * 10)]
	ldr r3,  [sp, #(8 * 11)]
	ldr r4,  [sp, #(8 * 12)]
	ldr r5,  [sp, #(8 * 13)]
	ldr r6,  [sp, #(8 * 14)]

	mov r8,  r0
	mov r9,  r1
	mov r10, r2
	mov r11, r3
	mov r12, r4
	mov r13, r5 // SP
	mov r14, r6 // LR

	ldr r0,  [sp, #(8 *  0)]
	ldr r1,  [sp, #(8 *  1)]
	ldr r2,  [sp, #(8 *  2)]
	ldr r3,  [sp, #(8 *  3)]
	ldr r4,  [sp, #(8 *  4)]
	ldr r5,  [sp, #(8 *  5)]
	ldr r6,  [sp, #(8 *  6)]
	ldr r7,  [sp, #(8 *  7)]

	add sp, sp, #(8 * 40)

	// load the measured time value to r0
	ldr r1, =_scamv_timeafter_store
	ldr r0, [r1]

	bx lr


#endif // RUN_CACHE

