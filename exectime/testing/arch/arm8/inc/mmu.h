#ifndef _MMU_H
#define _MMU_H


#include <stdint.h>

#define L1_PAGE_SIZE (1024*1024*1024)

void init_mmu();
uint64_t set_l1(void * l1);
void l1_set_translation(uint64_t * l1, uint64_t va, uint64_t pa, uint64_t cacheable);
void enable_mmu(void);
void disable_mmu(void);

#endif
