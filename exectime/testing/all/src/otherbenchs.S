
.align 3
eval3_entry:
//#include "/home/andreas/data/papers/bin_se_wcet/eval3/code.S"
// measures as 11 cycles in the benchmark for both (r0, r1) = (0, 0) | (1, 1)
nop
nop
nop
nop
nop

.global _alignmenttestfun_b16
.align 3
_alignmenttestfun_b16:
// start here: 40 cycles + ?

// select one of three experiments here
//nop
//nop
//b finished // this gives 4 extra cycles
cmp r0, r1
beq ait_e1 // this gives 12 extra cycles
b ait_e2 // this also gives 12 extra cycles

// ait gives 12, 18 and 19 cycles respectively


// aligned experiment
.align 3
ait_e1:
nop // need an extra nop to compensate the "early branch"
nop
nop
nop
b finished



// not aligned experiment
.align 3
nop // this breaks the alignment
ait_e2:
nop
nop
nop
b finished




nop
nop
nop

// we finish aligned
.align 3
finished:
bx lr


//-----------
//#include "/home/andreas/data/papers/bin_se_wcet/eval/code.S"
//-----------
/*
@ Vector table start
.long               0x20001000                     
.long               _start
@ Vector table end

_start:

loop:
    ADD R0, R0, #1
b loop
   
.global _start

*/


_start:
//  bl _f
loop:
  b loop

.globl _start

.macro pipelinewarmup10
  nop
  nop
  nop
  nop
  nop
  nop
.endm

  .global _reffunc_test0
  .align 3
_reffunc_test0: // takes 1, ait computes 7
  nop
  bx lr

  .global _reffunc_test1
  .align 3
_reffunc_test1: // takes 6, ait computes 12
  pipelinewarmup10
  bx lr

  .global _reffunc_test2
  .align 3
_reffunc_test2: // takes 7, ait computes 13
  pipelinewarmup10
  add r0, r1
  bx lr

  .global _reffunc_test3
  .align 3
_reffunc_test3: // takes 8, ait computes 14
  pipelinewarmup10
  add r0, r1
  sub r1, r2
  bx lr

  .global _reffunc_test4_9nopsubadd // benchmark executes 9 cycles
  .align 3
_reffunc_test4_9nopsubadd: // takes 9, ait computes 15
  pipelinewarmup10
  add r0, r1
  sub r1, r2
  sub r2, r3
  bx lr

  .global _reffunc_test5
  .align 3
_reffunc_test5: // takes 10, ait computes 16
  pipelinewarmup10
  add r0, r1
  sub r1, r2
  sub r2, r3
  sub r3, r4
  bx lr

  .global _reffunc_st
  .align 3
_reffunc_st: // takes 8, ait computes 15!!!
  //pipelinewarmup10
  str r0, [sp, #0]
  bx lr

  .global _reffunc_ld
  .align 3
_reffunc_ld: // takes 8, ait computes 15!!!
  //pipelinewarmup10
  ldr r0, [sp, #0]
  bx lr

  .global _reffunc_ld2_ldnop
  .align 3
_reffunc_ld2_ldnop: // takes 9, ait computes 15!!!
  //pipelinewarmup10
  ldr r0, [sp, #0]
  nop
  bx lr

  .global _reffunc_ld3
  .align 3
_reffunc_ld3: // takes 14, ait computes 19!!!
  pipelinewarmup10
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_jumphere
  .align 3
_reffunc_ld3_jumphere:
  nop
  bx lr

  .global _reffunc_ld4
  .align 3
_reffunc_ld4: // takes 24, ait computes 30!!!
  pipelinewarmup10
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  nop
  nop
  bx lr

  .global _reffunc_ld5_ldldbr8
  .align 3
_reffunc_ld5_ldldbr8: // takes 63, ait computes 61!!!
  //pipelinewarmup10
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j1
  .align 3
_reffunc_ld3_j1:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j2
  .align 3
_reffunc_ld3_j2:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j3
  .align 3
_reffunc_ld3_j3:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j4
  .align 3
_reffunc_ld3_j4:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j5
  .align 3
_reffunc_ld3_j5:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j6
  .align 3
_reffunc_ld3_j6:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j7
  .align 3
_reffunc_ld3_j7:
  ldr r0, [sp, #0]
  ldr r0, [sp, #0]
  b _reffunc_ld3_j8
  .align 3
_reffunc_ld3_j8:
  nop
  bx lr


  .global _reffunc_bx
  .align 3
_reffunc_bx: // takes 16, ait computes 21
  pipelinewarmup10
  ldr r0, =_reffunc_bx_jumphere
  mov r1, #1
  orr r0, r1
  ldr r2, =_reffunc_bx_jumphere
  bx r0
  .align 3
_reffunc_bx_jumphere:
  nop
  bx lr


  .global _reffunc_b16_00 // aligned
  .align 3
_reffunc_b16_00:
  b _reffunc_b16_00_j // aligned
  .global _reffunc_b16_10 // not aligned
  .align 3
_reffunc_b16_10:
  b _reffunc_b16_10_j // not aligned
// aligned experiment
.align 3
_reffunc_b16_00_j:
  nop // need an instruction here
  b _reffunc_b16_finished
// not aligned experiment
.align 3
  nop // this breaks the alignment
_reffunc_b16_10_j:
  nop // need an instruction here
  b _reffunc_b16_finished
// we finish aligned
.align 3
_reffunc_b16_finished:
  bx lr

#define USE_DIVMOD

//.extern __aeabi_idivmod

  //.thumb_func
  .global _mymodexp
  .align 3
// extra: r6, r7
_mymodexp:
  str r6, [sp, #0]
  sub sp, sp, #4
  str r7, [sp, #0]
  sub sp, sp, #4
// r3 => lr
  mov r3, lr
/*
M := st(M, SP, R3)                    // f(b, e, m): [prologue]
SP := SP $-$ 4
*/
  str r3, [sp, #0]
  sub sp, sp, #4
/*
M := st(M, SP, 1)                     // r := 1
*/
  mov r6, #1
  str r6, [sp, #0]
/*
R3 := 8                               // for i in 0 .. 7 {
*/
  mov r3, #8

l6:
/*
if R3 == 0 then goto 12
*/
  mov r6, #0
  cmp r3, r6
  beq l12
/*
R3 := R3 $-$ 1
*/
  sub r3, r3, #1
/*
if !((R0 >> R3) & 1) then goto 10     //   if e[i]
*/
  mov r6, r0
  lsr r6, r6, r3
  mov r7, #1
  and r6, r6, r7
  mov r7, #0
  cmp r6, r7
  beq l10
/*
M := st(M, SP, (ld(M, SP) * R1) % R2) //      r := (r*b)%m
*/
  ldr r6, [sp, #0]
  mul r6, r6, r1
  // mod r6, r6, r2
#ifdef USE_DIVMOD
  mov r8,  r0
  mov r9,  r1
  mov r10, r2
  mov r11, r3
  mov r0, r6
  mov r1, r2
//https://kolegite.com/EE_library/books_and_lectures/%D0%9F%D1%80%D0%BE%D0%B3%D1%80%D0%B0%D0%BC%D0%B8%D1%80%D0%B0%D0%BD%D0%B5/Assembly/ARM_calling_convention.pdf
  bl __aeabi_uidivmod //____aeabi_uidivmod_from_arm //(r1 := r0 % r1)
  mov r6, r1
  mov r0, r8
  mov r1, r9
  mov r2, r10
  mov r3, r11
#else
  sub r7, r2, #1
  and r6, r6, r7
#endif
  //
  str r6, [sp, #0]

l10:
/*
R1 := (R1 * R1) % R2                  //   b := (b*b)%m
*/
  mov r6, r1
  mul r6, r6, r6
  // mod r6, r6, r2
#ifdef USE_DIVMOD
  mov r8,  r0
  mov r9,  r1
  mov r10, r2
  mov r11, r3
  mov r0, r6
  mov r1, r2
  bl __aeabi_uidivmod //____aeabi_uidivmod_from_arm //(r1 := r0 % r1)
  mov r6, r1
  mov r0, r8
  mov r1, r9
  mov r2, r10
  mov r3, r11
#else
  sub r7, r2, #1
  and r6, r6, r7
#endif
  //
  mov r1, r6
/*
goto 6                                // }
*/
  b l6

l12:
/*
R0 := ld(M, SP)                       // return r
*/
  ldr r0, [sp, #0]
/*
SP := SP+4                            // [epilogue]
*/
  add sp, sp, #4
/*
R3 := ld(M, SP)
*/
  ldr r3, [sp, #0]
/*
goto R3
*/
  add sp, sp, #4
  ldr r7, [sp, #0]
  add sp, sp, #4
  ldr r6, [sp, #0]

  mov lr, r3
  bx lr

//.globl _mymodexp




  .global _reffunc_cjmp
  .align 3
_reffunc_cjmp:
  cmp r0, r1
  beq _reffunc_cjmp_jumphere
_reffunc_cjmp_jumphere:
  bx lr



