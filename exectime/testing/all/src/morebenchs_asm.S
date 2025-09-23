
// https://kolegite.com/EE_library/books_and_lectures/%D0%9F%D1%80%D0%BE%D0%B3%D1%80%D0%B0%D0%BC%D0%B8%D1%80%D0%B0%D0%BD%D0%B5/Assembly/ARM_calling_convention.pdf
// https://github.com/gcc-mirror/gcc/blob/master/libgcc/udivmodhi4.c
// https://stackoverflow.com/questions/30980160/arm-assembly-cannot-use-immediate-values-and-adds-adcs-together

//.syntax unified
.cpu cortex-m0

  //.thumb
  //.thumb_func
  .global _my_uidivmod_asm
  .align 3
_my_uidivmod_asm:
  // r0 is num
  // r1 is den
  // r2 is bit
  // r6 is res
  // r3 is i
  // r5 is flag
  mov r6, #0

  push	{r4, r5, r6, lr}
  movs	r3, #0
  movs	r5, #1
  movs	r2, #1
  b	_my_uidivmod_asm_n1 //b #0x14

_my_uidivmod_asm_n5:
  cmp	r2, #0
  beq	_my_uidivmod_asm_n2 //beq #0x1a
  cmp	r1, #0
  blt	_my_uidivmod_asm_n2 //blt #0x16
  movs	r3, r4
  lsl	r1, r1, #1
  lsl	r2, r2, #1

_my_uidivmod_asm_nb:
  cmp	r3, #32
  beq	_my_uidivmod_asm_n3 //beq #0x18

_my_uidivmod_asm_n1:
  add	r4, r3, #1
  cmp	r5, #0
  beq	_my_uidivmod_asm_n4 //beq #0x3a
  cmp	r0, r1
  bhi	_my_uidivmod_asm_n5 //bhi #0xffffffe6

_my_uidivmod_asm_n2:
  cmp	r4, #32
  beq	_my_uidivmod_asm_n3 //beq #0xa
  add	r3, #2
  movs	r5, #0
  cmp	r3, #32
  bne	_my_uidivmod_asm_n1 //bne #0xffffffec

_my_uidivmod_asm_n3:
  movs	r3, #32
  movs	r4, #1
  b	_my_uidivmod_asm_n6 //b #0x12

_my_uidivmod_asm_na:
  cmp	r0, r1
  blo	_my_uidivmod_asm_n7 //blo #4
  sub	r0, r0, r1
  //res |= bit;
  orr	r6, r6, r2

_my_uidivmod_asm_n7:
  lsr	r2, r2, #1
  lsr	r1, r1, #1

_my_uidivmod_asm_n9:
  sub	r3, #1
  cmp	r3, #0
  beq	_my_uidivmod_asm_n8 //beq #0x12

_my_uidivmod_asm_n6:
  cmp	r4, #0
  beq	_my_uidivmod_asm_n9 //beq #0xfffffff8
  cmp	r2, #0
  bne	_my_uidivmod_asm_na // bne #0xffffffea
  sub	r3, #1
  movs	r4, #0
  cmp	r3, #0
  bne	_my_uidivmod_asm_n6 //bne #0xfffffff2

_my_uidivmod_asm_n8:
  mov	r1, r0
  mov	r0, r6
  pop	{r4, r5, r6, pc}

_my_uidivmod_asm_n4:
  cmp	r4, #32
  beq	_my_uidivmod_asm_n3 //beq #0xffffffd6
  add	r3, #2
  b	_my_uidivmod_asm_nb //b #0xffffffb8

  // r is div
  // r0 is mod


//.globl _my_uidivmod_asm



  //.thumb_func
  .global _my_uidivmod_mod_asm
  .align 3
_my_uidivmod_mod_asm:
/*
  mov r4, lr
  bl _my_uidivmod_asm
  mov r0, r1
  bx r4
*/
  push	{r7, lr}
  sub	sp, #24
  add	r7, sp, #0
  str	r0, [r7, #4]
  str	r1, [r7, #0]
  mov	r3, #1
  str	r3, [r7, #20]
  mov	r3, #0
  str	r3, [r7, #16]
  mov	r3, #1
  str	r3, [r7, #12]
  mov	r3, #0
  str	r3, [r7, #8]
  b	_my_uidivmod_mod_asm_n1 // b #0x34

_my_uidivmod_mod_asm_n3:
  ldr	r3, [r7, #12]
  cmp	r3, #0
  beq	_my_uidivmod_mod_asm_n2 // beq #0x24
  ldr	r2, [r7, #0]
  ldr	r3, [r7, #4]
  cmp	r2, r3
  bhs	_my_uidivmod_mod_asm_n2 // bhs #0x1c
  ldr	r3, [r7, #20]
  cmp	r3, #0
  beq	_my_uidivmod_mod_asm_n2 // beq #0x16
  ldr	r3, [r7, #0]
  cmp	r3, #0
  blt	_my_uidivmod_mod_asm_n2 // blt #0x10
  ldr	r3, [r7, #0]
  lsl	r3, r3, #1
  str	r3, [r7, #0]
  ldr	r3, [r7, #20]
  lsl	r3, r3, #1
  str	r3, [r7, #20]
  b	_my_uidivmod_mod_asm_n9 // b #6

_my_uidivmod_mod_asm_n2:
  mov	r3, #0
  str	r3, [r7, #12]

_my_uidivmod_mod_asm_n9:
  ldr	r3, [r7, #8]
  add	r3, #1
  str	r3, [r7, #8]

_my_uidivmod_mod_asm_n1:
  ldr	r3, [r7, #8]
  cmp	r3, #31
  ble	_my_uidivmod_mod_asm_n3 // ble #0xffffffca
  mov	r3, #1
  str	r3, [r7, #12]
  mov	r3, #0
  str	r3, [r7, #8]
  b	_my_uidivmod_mod_asm_n4 // b #0x3e

_my_uidivmod_mod_asm_n8:
  ldr	r3, [r7, #12]
  cmp	r3, #0
  beq	_my_uidivmod_mod_asm_n5 // beq #0x2e
  ldr	r3, [r7, #20]
  cmp	r3, #0
  beq	_my_uidivmod_mod_asm_n5 // beq #0x28
  ldr	r2, [r7, #4]
  ldr	r3, [r7, #0]
  cmp	r2, r3
  blo	_my_uidivmod_mod_asm_n6 // blo #0x12
  ldr	r2, [r7, #4]
  ldr	r3, [r7, #0]
  sub	r3, r2, r3
  str	r3, [r7, #4]
  ldr	r2, [r7, #16]
  ldr	r3, [r7, #20]
  orr	r3, r2
  str	r3, [r7, #16]

_my_uidivmod_mod_asm_n6:
  ldr	r3, [r7, #20]
  lsr	r3, r3, #1
  str	r3, [r7, #20]
  ldr	r3, [r7, #0]
  lsr	r3, r3, #1
  str	r3, [r7, #0]
  b	_my_uidivmod_mod_asm_n7 // b #6

_my_uidivmod_mod_asm_n5:
  mov	r3, #0
  str	r3, [r7, #12]

_my_uidivmod_mod_asm_n7:
  ldr	r3, [r7, #8]
  add	r3, #1
  str	r3, [r7, #8]

_my_uidivmod_mod_asm_n4:
  ldr	r3, [r7, #8]
  cmp	r3, #31
  ble	_my_uidivmod_mod_asm_n8 // ble #0xffffffc0
  ldr	r3, [r7, #4]
  mov	r0, r3
  mov	sp, r7
  add	sp, #24
  pop	{r7, pc}

//.globl _my_uidivmod_mod_asm





  //.thumb_func
  .global _my_modexp_asm
  .align 3
  // uses r0-3, r4, r5, r6
_my_modexp_asm:
  push {r4,r5,r6}
  mov r6, #32
 
 //SP := SP $-$ 8                        // f(e, b, m): [prologue]
 //M := st(M, SP + 4, R3)
 //M := st(M, SP, 1)                     // r := 1
  sub sp, sp, #8
  mov r5, lr
  str r5, [sp, #4]
  mov r5, #1
  str r5, [sp, #0]


 //R3 := 0                               // for i in 0 .. 31 {
  mov r3, #0

_my_modexp_loop:
 //if !((R0 >> R3) & 1) goto 7 else 8    //   if e[i]
  mov r4, r0
  lsr r4, r4, r3
  mov r5, #1
  and r4, r4, r5
  cmp r4, r5 // could probably save this instruction with ands before and beq (test for zero result)
  bne _my_modexp_branch_skip

 //M := st(M, SP, (ld(M, SP) * R1) % R2) //      r := (r*b)%m
  ldr r4, [sp, #0]
  mul r4, r4, r1
  push {r0,r1,r2,r3}
  mov r0, r4
  mov r1, r2
  bl _my_uidivmod_mod_asm
  mov r4, r0
  pop {r0,r1,r2,r3}
  str r4, [sp, #0]
 
_my_modexp_branch_skip:
 //R1 := (R1 * R1) % R2                  //   b := (b*b)%m
  mov r4, r1
  mul r4, r4, r1
  push {r0,r1,r2,r3}
  mov r0, r4
  mov r1, r2
  bl _my_uidivmod_mod_asm
  mov r4, r0
  pop {r0,r1,r2,r3}
  mov r1, r4

 //R3 := R3 + 1                          // }
  add r3, r3, #1

 //if R3 == 32 goto 11 else 6
  cmp r3, r6
  bne _my_modexp_loop


_my_modexp_loop_done:
 //R0 := ld(M, SP)                       // return r [epilogue]
  ldr r0, [sp, #0]

 //R3 := ld(M, SP + 4)
  ldr r5, [sp, #4]
  mov lr, r5

 //SP := SP + 8
  add sp, sp, #8

  pop {r4,r5,r6}

 //goto R3
  bx lr

//.globl _my_modexp_asm








  //.thumb_func
  .global _motor_prep_input
  .align 3
  // uses ...
_motor_prep_input:
push	{r7, lr}
sub	sp, #16
add	r7, sp, #0
str	r0, [r7, #4]
ldr	r3, [r7, #4]
lsr	r3, r3, #31
uxtb	r2, r3
movs	r1, #15
add	r3, r7, r1
strb	r2, [r3, #0]
add	r3, r7, r1
ldrb	r3, [r3, #0]
cmp	r3, #0
beq	_motor_prep_input_l1
ldr	r3, [r7, #4]
neg	r3, r3
str	r3, [r7, #4]

_motor_prep_input_l1:
ldr	r3, [r7, #4]
ldr	r2, =0x00001770
cmp	r3, r2
ble	_motor_prep_input_l2
ldr	r3, =0x00001770

_motor_prep_input_l2:
str	r3, [r7, #4]
ldr	r3, [r7, #4]
ldr	r2, =0x00001770
sub	r3, r2, r3
str	r3, [r7, #4]
ldr	r3, [r7, #4]
movs	r0, r3
mov	sp, r7
add	sp, #16
pop	{r7, pc}



  //.thumb_func
  .global _motor_prep_input_mod
  .align 3
  // uses ...
/*
_motor_prep_input_mod:
push	{r7, lr}                     // 3
sub	sp, #16                      // 1
add	r7, sp, #0                   // 1
str	r0, [r7, #4]                 // 2
ldr	r3, [r7, #4]                 // 2
lsr	r3, r3, #31                  // 1
uxtb	r2, r3                       // 1
movs	r1, #15                      // 1
add	r3, r7, r1                   // 1
strb	r2, [r3, #0]                 // 2
add	r3, r7, r1                   // 1
ldrb	r3, [r3, #0]                 // 2
cmp	r3, #0                       // 1
beq	_motor_prep_input_mod_l1     // 1/3
ldr	r3, [r7, #4]                 // 2
neg	r3, r3                       // 1
str	r3, [r7, #4]                 // 2

_motor_prep_input_mod_l1:
ldr	r3, [r7, #4]                 // 2
ldr	r2, =0x00001770              // 2
cmp	r3, r2                       // 1
ble	_motor_prep_input_mod_l2     // 1/3
ldr	r3, =0x00001770              // 2

_motor_prep_input_mod_l2:
str	r3, [r7, #4]                 // 2
ldr	r3, [r7, #4]                 // 2
ldr	r2, =0x00001770              // 2
sub	r3, r2, r3                   // 1
str	r3, [r7, #4]                 // 2
ldr	r3, [r7, #4]                 // 2
movs	r0, r3                       // 1
mov	sp, r7                       // 1
add	sp, #16                      // 1
pop	{r7, pc}                     // 3
*/



_motor_prep_input_mod:
push	{r7, lr}                     // 3
sub	sp, #16                      // 1
mov	r3, #4                   // 1
add	r7, sp, #0                   // 1
//add	r3, #4                   // 1
str	r2, [r7, #0]
ldr	r3, [r7, #0]
add	sp, #16                      // 1
pop	{r7, pc}                     // 3






