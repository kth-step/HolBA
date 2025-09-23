#include "config.h"

#ifdef RUN_CACHE

#if !defined(__has_include)
#  error "need __has_include"
#endif

#if (!__has_include("experiment/asm.h")) || (!__has_include("experiment/asm_setup_1.h"))
#  error "need at least asm code to run and asm code to setup state 1"
#endif

#if __has_include("experiment/asm_setup_train.h")
#  define EXP_HAS_INPUT_TRAIN
#endif

#if __has_include("experiment/asm_setup_2.h")
#  define EXP_HAS_INPUT_2
#endif

.globl _cache_run

#ifdef EXP_HAS_INPUT_TRAIN
.globl _scamv_train
#endif
.globl _scamv_run1
#ifdef EXP_HAS_INPUT_2
.globl _scamv_run2
#endif

.section .experiment_code
scamv_entry:
.include "experiment/asm.h"
	b scamv_exit


.section .data
.align 3
_sp_store:
	.quad 0
.align 3
_scamv_ret_store:
	.quad 0
.align 3
_scamv_train_loop_cnt:
	.quad 0


.section .text

#ifdef EXP_HAS_INPUT_TRAIN
_scamv_train:
	ldr x0, =_scamv_ret_store
	str x30, [x0]
	mov x0,  #0
	mov x30, #0
.include "experiment/asm_setup_train.h"
	dsb sy
	isb
	b scamv_entry
#endif // EXP_HAS_INPUT_TRAIN

_scamv_run1:
	ldr x0, =_scamv_ret_store
	str x30, [x0]
	mov x0,  #0
	mov x30, #0
.include "experiment/asm_setup_1.h"
	dsb sy
	isb
	b scamv_entry

#ifdef EXP_HAS_INPUT_2
_scamv_run2:
	ldr x0, =_scamv_ret_store
	str x30, [x0]
	mov x0,  #0
	mov x30, #0
.include "experiment/asm_setup_2.h"
	dsb sy
	isb
	b scamv_entry
#endif // EXP_HAS_INPUT_2

scamv_exit:
	dsb sy
	isb
	ldr x0, =_scamv_ret_store
	ldr x30, [x0]
	ret


_cache_run:
// save registers on stack
	sub sp, sp, #(8 * 40)
	str x0,  [sp, #(8 *  0)] // cache
	str x1,  [sp, #(8 *  1)] // _clean_mem_run
	str x2,  [sp, #(8 *  2)] // _scamv_run
	str x3,  [sp, #(8 *  3)] // _clean_mem_train
	str x4,  [sp, #(8 *  4)] // _scamv_train
	str x5,  [sp, #(8 *  5)]
	str x6,  [sp, #(8 *  6)]
	str x7,  [sp, #(8 *  7)]
	str x8,  [sp, #(8 *  8)]
	str x9,  [sp, #(8 *  9)]
	str x10, [sp, #(8 * 10)]
	str x11, [sp, #(8 * 11)]
	str x12, [sp, #(8 * 12)]
	str x13, [sp, #(8 * 13)]
	str x14, [sp, #(8 * 14)]
	str x15, [sp, #(8 * 15)]
	str x16, [sp, #(8 * 16)]
	str x17, [sp, #(8 * 17)]
	str x18, [sp, #(8 * 18)]
	str x19, [sp, #(8 * 19)]
	str x20, [sp, #(8 * 20)]
	str x21, [sp, #(8 * 21)]
	str x22, [sp, #(8 * 22)]
	str x23, [sp, #(8 * 23)]
	str x24, [sp, #(8 * 24)]
	str x25, [sp, #(8 * 25)]
	str x26, [sp, #(8 * 26)]
	str x27, [sp, #(8 * 27)]
	str x28, [sp, #(8 * 28)]
	str x29, [sp, #(8 * 29)] // FP
	str x30, [sp, #(8 * 30)] // LR

// store SP register
	ldr x0, =_sp_store
	mov x1, sp
	str x1, [x0]

#ifdef EXP_HAS_INPUT_TRAIN
// ========================================================

	ldr x0, =_scamv_train_loop_cnt
	mov x1, #0
	str x1, [x0]

__enter_scamv_train_loop:
	ldr x0, =_scamv_train_loop_cnt
	ldr x1, [x0]
	mov x2, #6
	cmp x1, x2
	b.ge __exit_scamv_train_loop
	add x1, x1, #1
	str x1, [x0]

// restore SP register
	ldr x0, =_sp_store
	ldr x1, [x0]
	mov sp, x1
// flush the cache
	//flush_d_cache(0);
	mov x0, #0
	bl flush_d_cache
	//flush_d_cache(1);
	mov x0, #1
	bl flush_d_cache
// clean experiment memory: _clean_mem_run
	ldr x30, [sp, #(8 *  3)]
	blr x30
// load _scamv_run in x30 (LR)
	ldr x30, [sp, #(8 *  4)]
// create defined processor state
	mov x0,  #0
	mov x1,  #0
	mov x2,  #0
	mov x3,  #0
	mov x4,  #0
	mov x5,  #0
	mov x6,  #0
	mov x7,  #0
	mov x8,  #0
	mov x9,  #0
	mov x10, #0
	mov x11, #0
	mov x12, #0
	mov x13, #0
	mov x14, #0
	mov x15, #0
	mov x16, #0
	mov x17, #0
	mov x18, #0
	mov x19, #0
	mov x20, #0
	mov x21, #0
	mov x22, #0
	mov x23, #0
	mov x24, #0
	mov x25, #0
	mov x26, #0
	mov x27, #0
	mov x28, #0
	mov x29, #0
	mov sp,  x0
	// set all ALU flags to a defined state
	adds x0, x1, x2

// run the experiment code (with training inputs)
	blr x30
	b __enter_scamv_train_loop

__exit_scamv_train_loop:

// ========================================================
#endif // EXP_HAS_INPUT_TRAIN

// restore SP register
	ldr x0, =_sp_store
	ldr x1, [x0]
	mov sp, x1
// flush the cache
	//flush_d_cache(0);
	mov x0, #0
	bl flush_d_cache
	//flush_d_cache(1);
	mov x0, #1
	bl flush_d_cache
// clean experiment memory: _clean_mem_run
	ldr x30, [sp, #(8 *  1)]
	blr x30
// load _scamv_run in x30 (LR)
	ldr x30, [sp, #(8 *  2)]
// create defined processor state
	mov x0,  #0
	mov x1,  #0
	mov x2,  #0
	mov x3,  #0
	mov x4,  #0
	mov x5,  #0
	mov x6,  #0
	mov x7,  #0
	mov x8,  #0
	mov x9,  #0
	mov x10, #0
	mov x11, #0
	mov x12, #0
	mov x13, #0
	mov x14, #0
	mov x15, #0
	mov x16, #0
	mov x17, #0
	mov x18, #0
	mov x19, #0
	mov x20, #0
	mov x21, #0
	mov x22, #0
	mov x23, #0
	mov x24, #0
	mov x25, #0
	mov x26, #0
	mov x27, #0
	mov x28, #0
	mov x29, #0
	mov sp,  x0
	// set all ALU flags to a defined state
	adds x0, x1, x2

// run the experiment code
	blr x30
// restore SP register
	ldr x0, =_sp_store
	ldr x1, [x0]
	mov sp, x1
// save the cache state for run
	//save_cache_state(cache);
	ldr x0,  [sp, #(8 *  0)]
	bl save_cache_state

/*
// debug the first cache set
	//debug_set(cache1[0]);
	ldr x0,  [sp, #(8 *  0)]
	mov x1, #0
	bl debug_set
*/

// restore registers from stack
	ldr x0,  [sp, #(8 *  0)]
	ldr x1,  [sp, #(8 *  1)]
	ldr x2,  [sp, #(8 *  2)]
	ldr x3,  [sp, #(8 *  3)]
	ldr x4,  [sp, #(8 *  4)]
	ldr x5,  [sp, #(8 *  5)]
	ldr x6,  [sp, #(8 *  6)]
	ldr x7,  [sp, #(8 *  7)]
	ldr x8,  [sp, #(8 *  8)]
	ldr x9,  [sp, #(8 *  9)]
	ldr x10, [sp, #(8 * 10)]
	ldr x11, [sp, #(8 * 11)]
	ldr x12, [sp, #(8 * 12)]
	ldr x13, [sp, #(8 * 13)]
	ldr x14, [sp, #(8 * 14)]
	ldr x15, [sp, #(8 * 15)]
	ldr x16, [sp, #(8 * 16)]
	ldr x17, [sp, #(8 * 17)]
	ldr x18, [sp, #(8 * 18)]
	ldr x19, [sp, #(8 * 19)]
	ldr x20, [sp, #(8 * 20)]
	ldr x21, [sp, #(8 * 21)]
	ldr x22, [sp, #(8 * 22)]
	ldr x23, [sp, #(8 * 23)]
	ldr x24, [sp, #(8 * 24)]
	ldr x25, [sp, #(8 * 25)]
	ldr x26, [sp, #(8 * 26)]
	ldr x27, [sp, #(8 * 27)]
	ldr x28, [sp, #(8 * 28)]
	ldr x29, [sp, #(8 * 29)]
	ldr x30, [sp, #(8 * 30)]
	add sp, sp, #(8 * 40)

	ret


#endif // RUN_CACHE

