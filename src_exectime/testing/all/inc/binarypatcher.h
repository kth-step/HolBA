#ifndef BINARYPATCHER_H
#define BINARYPATCHER_H

void patch_arm8_br(uint64_t instr_addr, uint64_t jump_target);

#endif // BINARYPATCHER_H

