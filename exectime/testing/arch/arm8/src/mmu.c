#include "mmu.h"

void init_mmu() {
  // Initialize translation table control registers
  unsigned int val = 0x3520;
  asm (
       "MSR TCR_EL3, %x[input_i]"
       :
       : [input_i] "r" (val)
       );
  // 4GB space 4KB granularity for L2
  // Inner-shareable.
  // Normal Inner and Outer Cacheable.

  val = 0xFF440400;
  asm (
       "MSR MAIR_EL3, %x[input_i]"
       :
       : [input_i] "r" (val)
       );
  // ATTR0 Device-nGnRnE ATTR1 Device.
  // ATTR2 Normal Non-Cacheable. 
  // ATTR3 Normal Cacheable.
}

uint64_t set_l1(void * l1) {
  uint64_t l1_pt_add = (uint64_t)l1;
  // l1_lage_table must be a 4KB-aligned address.
  asm (
       "MSR TTBR0_EL3, %x[input_i]"
       :
       : [input_i] "r" (l1_pt_add)
       );
  return 0;
}


void l1_set_translation(uint64_t * l1, uint64_t va, uint64_t pa, uint64_t cacheable) {
  uint64_t idx = (va / L1_PAGE_SIZE);
  // the physical address to map to is the base entry value (aligning it to the l1 page size)
  uint64_t entry = (pa / L1_PAGE_SIZE) * L1_PAGE_SIZE;
  if (cacheable == 0)
    entry |= 0x00000741;
  else
    entry |= 0x0000074D;
  l1[idx] = entry;
}

void enable_mmu(void) {
    // It is implemented in the CPUECTLR register.
  uint64_t smp;
  asm (
       "MRS %x[result], S3_1_C15_C2_1"
       : [result] "=r" (smp)
       : 
       );
  smp |= (0x1 << 6); // The SMP bit.
  asm (
       "MSR S3_1_C15_C2_1, %x[input_i]"
       :
       : [input_i] "r" (smp)
       );
  
  // Enable caches and the MMU.
  uint64_t sctl;
  asm (
       "MRS %x[result], SCTLR_EL3"
       : [result] "=r" (sctl)
       : 
       );
  sctl |= 0x1 << 0;  // The M bit (MMU).
  sctl |= 0x1 << 1;  // The A bit (alignment check for memory accesses).
  sctl |= 0x1 << 2;  // The C bit (data cache).
  sctl |= 0x1 << 12; // The I bit (instruction cache).
  asm (
       "MSR SCTLR_EL3, %x[input_i]"
       :
       : [input_i] "r" (sctl)
       );
  asm (
       "DSB SY"
       :
       :
       );
  asm (
       "ISB"
       :
       :
       );
}

void disable_mmu(void) {
    // It is implemented in the CPUECTLR register.
  uint64_t smp;
  asm (
       "MRS %x[result], S3_1_C15_C2_1"
       : [result] "=r" (smp)
       : 
       );
  smp |= (0x1 << 6); // The SMP bit.
  asm (
       "MSR S3_1_C15_C2_1, %x[input_i]"
       :
       : [input_i] "r" (smp)
       );
  
  // Enable caches and the MMU.
  uint64_t sctl;
  asm (
       "MRS %x[result], SCTLR_EL3"
       : [result] "=r" (sctl)
       : 
       );
  sctl &= ~(0x1 << 0);  // The M bit (MMU).
  sctl |=   0x1 << 1;   // The A bit (alignment check for memory accesses).
  sctl &= ~(0x1 << 2);  // The C bit (data cache).
  sctl &= ~(0x1 << 12); // The I bit (instruction cache).
  asm (
       "MSR SCTLR_EL3, %x[input_i]"
       :
       : [input_i] "r" (sctl)
       );
  asm (
       "DSB SY"
       :
       :
       );
  asm (
       "ISB"
       :
       :
       );
}
