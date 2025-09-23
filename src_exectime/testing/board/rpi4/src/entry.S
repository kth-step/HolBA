/*
 * Derived from code with this copyright notice:
 *
 * Copyright (c) 2016 Stephen Warren <swarren@wwwdotorg.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * * Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * * Neither the name of the copyright holder nor the names of its contributors
 *   may be used to endorse or promote products derived from this software
 *   without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

.globl _start
.globl _embexp_entry

_embexp_entry:
_start:
	b cores0123

	// an infinite loop at location 0x4 (to catch all cores here after initialization)
	// (if we use a more sophisticated loop with "wfe" or a more involved one,
        //  we may need an exit strategy with a flag or something I guess)
hang:
	b hang


cores0123:
	// all four cores are executing from here

	// ==========================================================
	// enable NEON and FP registers
	// p50: http://infocenter.arm.com/help/topic/com.arm.doc.dai0527a/DAI0527A_baremetal_boot_code_for_ARMv8_A_processors.pdf

	// Disable trapping of accessing in EL3 and EL2.
	MSR CPTR_EL3, XZR
	MSR CPTR_EL3, XZR // should this not be CPTR_EL2?
	// Disable access trapping in EL1 and EL0.
	MOV X1, #(0x3 << 20) // FPEN disables trapping to EL1.
	MSR CPACR_EL1, X1
	ISB
	// ==========================================================

	// first, we need to stop all cores except core0
	mrs x2, MPIDR_EL1
	and x2, x2, #0xFF
	cbnz x2, cores123

	// set exception vector base address
	adr x0, vectors
	msr vbar_el3, x0
	msr vbar_el2, x0
	msr vbar_el1, x0

	// then, core0 can move on to execute the main c function
	ldr x5, =__stack_memory_top
	mov sp, x5
	bl main
	b hang





cores123:
	sub x2, x2, #1
	cbnz x2, cores23
	// only core 1 continues

	ldr x5, =0x00200000
	mov sp, x5
	bl main_core1
	b hang


cores23:
	sub x2, x2, #1
	cbnz x2, cores3
	// only core 2 continues

	ldr x5, =0x00300000
	mov sp, x5
	bl main_core2
	b hang


cores3:
	sub x2, x2, #1
	cbnz x2, hang
	// only core 3 continues

	ldr x5, =0x00400000
	mov sp, x5
	bl main_core3
	b hang






