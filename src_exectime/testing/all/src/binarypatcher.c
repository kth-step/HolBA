#include <stdint.h>

#include "config.h"

#ifdef __PROGPLAT_ARCH__ARM8

void patch_arm8_br(uint64_t instr_addr, uint64_t jump_target) {
  // inputs must be evenly divisible by 4
  if (((instr_addr % 4) != 0) || ((jump_target % 4) != 0))
    while (1);

  //uint64_t instr_addr = 0x200038;
  //uint64_t jump_target = 0x2004;
  // ensure 63 bits
  if ((instr_addr >> 63) || (jump_target >> 63))
    while (1);
  int64_t jump_diff = (int64_t)jump_target - (int64_t)instr_addr;

  // check that jump_diff is evenly divisible by 4
  // (this is redundant)
  if ((jump_diff % 4) != 0)
    while (1);

  // check that jump_diff fits in 3 bytes + 2 bits
  // (we overapproximate this a bit and check only if the absolute value fits into 25 bits - it's okay because we won't need the these long jumps in our application)
  int32_t jump_imm_enc = jump_diff / 4;
  int32_t jump_imm_enc_abs = jump_imm_enc >= 0 ? jump_imm_enc : -jump_imm_enc;
  if ((jump_imm_enc_abs & (~0x01FFFFFF)) != 0)
    while (1);

  uint32_t instr_opc = (0x14 << 24);
  uint32_t instr_imm = (jump_imm_enc & 0x03FFFFFF);

  *((uint32_t*)(instr_addr)) = instr_opc | instr_imm;
}

/*

in "testing/binaryloader":
> make clean all

debugging with gdb:
> make clean debug

x 0x200018
b *0x200000
continue
x 0x200018
x/i 0x200018

detach
quit

*/

#endif

