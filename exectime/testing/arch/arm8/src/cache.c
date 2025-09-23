#include "cache.h"
#include "lib/printf.h"

#define BARRIER_DSB_ISB() __asm__ __volatile__("DSB SY \t\n ISB \t\n")

void flush_d_cache(uint64_t level) {
  uint64_t nways = (level == 0)?WAYS:WAYS_L2;
  uint64_t nsets = (level == 0)?SETS:SETS_L2;
  
  // add	x2, x2, #4		/* x2 <- log2(cache line size) */
  uint64_t x2 = 6;
  // clz	w5, w3			/* bit position of #ways */
  uint64_t x5;
  asm (
       "clz %x[result], %x[input_i]"
       : [result] "=r" (x5)
       : [input_i] "r" (nways-1)
       );
  x5 -= 32;
  // uint64_t x5 = 29;
  //and	x4, x4, x6, lsr #13	/* x4 <- max number of #sets */
  /* x12 <- cache level << 1 */
  uint64_t x12 = (level << 1);
  /* x2 <- line length offset */
  /* x3 <- number of cache ways - 1 */
  /* x4 <- number of cache sets - 1 */
  /* x5 <- bit position of #ways */

  for (uint64_t set=0; set < nsets; set++) {
    //loop_set:
    //	mov	x6, x3			/* x6 <- working copy of #ways */
    //loop_way:
    for (uint64_t x6=0; x6<nways; x6 ++ ) {
      //	lsl	x7, x6, x5
      uint64_t x7 = x6 << x5;
      // orr	x9, x12, x7		/* map way and level to cisw value */
      volatile uint64_t x9 = x12 | x7;
      // lsl	x7, x4, x2
      x7 = set << x2;
      // orr	x9, x9, x7		/* map set number to cisw value */
      x9 = x9 | x7;
      asm (
           "dc	cisw, %x[input_i]"
           :
           : [input_i] "r" (x9)
           );
    }
  }

  BARRIER_DSB_ISB();
}


void get_cache_line(cache_line *line, uint64_t set, uint64_t way) {
  volatile uint64_t value;
  BARRIER_DSB_ISB();

  for (uint64_t  offset=0; offset<8; offset++) {
    value = 0;
    value |= (0b11 & way) << 30;
    value |= (0b111111111111111111111111 & set) << 6;
    value |= (0b111 & offset) << 3;

    // printf("accessing cache line value is %b\n", value);

    asm (
         "MSR S3_3_C15_C4_0, %x[input_i]"
         :
         : [input_i] "r" (value)
         );
    // Reading data
    asm (
         "MRS %x[result], S3_3_C15_C0_0"
         : [result] "=r" (value)
         : 
         );
    line->data[offset] = value;
    asm (
         "MRS %x[result], S3_3_C15_C0_1"
         : [result] "=r" (value)
         : 
         );
    line->data[offset] |= (value << 32);
  }
  // getting info
  value = 0;
  value |= (0b11 & way) << 30;
  value |= (0b111111111111111111111111 & set) << 6;

  asm (
       "MSR S3_3_C15_C2_0, %x[input_i]"
       :
       : [input_i] "r" (value)
       );
  
  asm (
       "MRS %x[result], S3_3_C15_C0_0"
       : [result] "=r" (value)
       : 
       );

  line->r0 = value;

  line->tag = 0;
  line->tag = ((0x80000000 & value) >> 31) << 11;
  asm (
       "MRS %x[result], S3_3_C15_C0_1"
       : [result] "=r" (value)
       : 
       );
  line->r1 = value;
  line->tag |= ((0xfffffff&value) << 12);
  line->tag += set * 64;

  line->valid = (((0x60000000 & value) >> 29) != 0);

  BARRIER_DSB_ISB();
}


/* Page 183- ARMv8 Cortex-a72 reference manual: L1-D Data RAM. */
/*   31-24: RAMID = 0x09 */
/*   23-19: Reserved     */
/*   18: Way select      */
/*   17-14: Unused       */
/*   13-6: Set select    */
/*   5-4: Bank select    */
/*   3: Upper or lower doubleword within the quadword */
/*   2-0: Reserved       */
// DL1DATA1[31:0] Data word 1.
// DL1DATA0[31:0] Data word 0.

/* Page 183- ARMv8 Cortex-a72 reference manual: L1-D Tag RAM. */
/*   31-24: RAMID = 0x08 */
/*   23-19: Reserved     */
/*   18: Way select      */
/*   17-14: Unused       */
/*   13-8: Row select    */
/*   7-6: Bank select    */
/*   5-0: Reserved       */
// DL1DATA1[1:0] MESI state:
// -- 0b00 Invalid.
// -- 0b01 Exclusive.
// -- 0b10 Shared.
// -- 0b11 Modified.
// DL1DATA0[30]   Non-secure identifier for the physical address.
// DL1DATA0[29:0] Physical address tag [43:14].

void get_cache_line_a72(cache_line *line, uint64_t set, uint64_t way) {
  volatile uint64_t value;
  BARRIER_DSB_ISB();

  for (uint64_t  bank = 0; bank < 8; bank++) { 
    value = 0;
    value |= (0b11111111 & 0x09) << 24;
    value |= (0b1 & way) << 18;
    value |= (0b11111111 & set) << 6;
    value |= (0b111 & bank) << 3;
    /* printf("Accessedg cache line value is %b\n", value); */
    asm (/* Instead of LDR pseudo-instruction I directly pass the address to SYS instruction */
	       "SYS #0, C15, C4, #0, %x[input_i]"
	       :
	       : [input_i] "r" (value)
	       );
    BARRIER_DSB_ISB();

    // Reading data
    asm (
	       "MRS %x[result], S3_0_C15_C1_0"
	       : [result] "=r" (value)
	       :
	       );
    line->data[bank] = value;
    asm (
	       "MRS %x[result], S3_0_C15_C1_1"
	       : [result] "=r" (value)
	       :
	       );
    line->data[bank] |= (value << 32);
  }
  
  // get info
  value = 0;
  value |= (0b11111111 & 0x08) << 24;
  value |= (0b1 & way) << 18;
  value |= (0b11111111 & set) << 6;

  asm (
       "SYS #0, C15, C4, #0, %x[input_i]"
       :
       : [input_i] "r" (value)
       );
  BARRIER_DSB_ISB();
  // Reading data
  asm (
       "MRS %x[result], S3_0_C15_C1_0"
       : [result] "=r" (value)
       :
       );
  line->r0 = value;
  line->tag = ((0x3FFFFFFF&value) << 14);  
  line->tag += set * 64; // TODO: what is this? whitout this tag from rpi3 and rpi4 are not equal

  asm (
       "MRS %x[result], S3_0_C15_C1_1"
       : [result] "=r" (value)
       :
       );
  line->r1 = value;
  line->valid = (((0x00000003 & value) << 29) != 0);

  BARRIER_DSB_ISB();

  return;
}


uint64_t get_prefetching_conf() {
  uint64_t volatile value;
  asm (
       "MRS %x[result], S3_1_C15_C2_0"
       : [result] "=r" (value)
       : 
       );
  return value;
}


prefetch_conf parse_prefetch_conf(uint64_t conf) {
  prefetch_conf res;
  res.NPFSTRM = (conf >> 19) & 0b11;
  res.STRIDE  = (conf >> 17) & 0b1;
  res.L1PCTL  = (conf >> 13) & 0b111;
  return res;
}

uint64_t set_prefetching_conf(uint64_t conf, prefetch_conf new_conf) {
  uint64_t mask = ~((0b11<<19) | (0b1<<17) | (0b111<<13));
  //printf("mask %b \n", mask);
  conf &= mask;
  conf |= (((uint64_t)new_conf.NPFSTRM) & 0b11) << 19;
  conf |= (((uint64_t)new_conf.STRIDE) & 0b1) << 17;
  uint64_t new_L1PCTL = (((uint64_t)new_conf.L1PCTL) & 0b111) << 13;
  printf("new_L1PCTL %b \n", new_L1PCTL);
  conf = conf | new_L1PCTL;
  printf("new_conf %b \n", conf);
  
  uint64_t volatile value = conf;
  asm (
       "MSR S3_1_C15_C2_0, %x[input_i]"
       :
       : [input_i] "r" (value)
       );
  return conf;
}



void save_cache_state(cache_state cache) {
  BARRIER_DSB_ISB();

  for (int set=0; set<SETS; set++) {
    for (int way=0; way<WAYS; way++) {
    #ifdef CORTEX_A72
      get_cache_line_a72(&(cache[set][way]), set, way);
    #else
      get_cache_line(&(cache[set][way]), set, way);
    #endif
    }
  }

  BARRIER_DSB_ISB();
}



void debug_line(cache_line * line, _Bool values) {
  uint64_t i;
  printf(" tag: %x\n", line->tag);
  printf(" valid: %d\n", (line->valid));
  if (values) {
    printf(" values:");
    for (i=0; i<8; i++) {
      printf(" %x-%x", (line->data[i] >> 32), line->data[i]);
    }
    printf("\n");
  }
  printf(" regs: %x-%x %x-%x\n", (line->r0 >> 32), line->r0, (line->r1 >> 32), line->r1);

}

void debug_line_info(cache_line * line) {
  if (!line->valid)
    return;

  printf(" tag: %x\n", line->tag);
  printf(" regs: %x-%x %x-%x\n", (line->r0 >> 32), line->r0, (line->r1 >> 32), line->r1);

}

void debug_set(set_t set, _Bool values) {
  uint64_t i;
  printf("Debugging set\n");
  for (i=0; i<WAYS; i++) {
    debug_line(&(set[i]), values);
  }
}

void debug_set_info(set_t set) {
  uint64_t i;
  printf("Info set\n");
  for (i=0; i<WAYS; i++) {
    debug_line_info(&(set[i]));
  }
}

void print_cache_full(cache_state c) {
  printf("----\n");
  printf("print_cache_full\n");
  printf("----\n");
  for (uint64_t set=0; set<SETS; set++) {
    printf("set=%d\n", set);
    for (uint64_t way=0; way<WAYS; way++) {
      printf("line=%d\n", way);
      debug_line(&c[set][way], 0);
    }
  }
  printf("----\n");
}

void print_cache_valid(cache_state c) {
  printf("----\n");
  printf("print_cache_valid\n");
  printf("----\n");
  for (uint64_t set=0; set<SETS; set++) {
    for (uint64_t way=0; way<WAYS; way++) {
      cache_line * l1 = &c[set][way];
      if (l1->valid) {
        printf("%i\t::%i\t:: tag: %x\n", set, way, l1->tag);
      }
    }
  }
  printf("----\n");
}

cache_line * get_line_for_pa(cache_state cache, uint64_t pa) {
  uint64_t set = SET(pa);
  for (int way=0; way<WAYS; way++) {
    if (!cache[set][way].valid)
      continue;
    if ((cache[set][way].tag / 64) == (pa / 64))
      return &(cache[set][way]);
  }
  return 0;
}

int hit_for_pa(cache_state cache, uint64_t pa) {
  cache_line * line = get_line_for_pa(cache, pa);
  return (line != 0);
}


uint64_t compare_cache(cache_state c1, cache_state c2) {
  return compare_cache_bounds(c1, c2, 0, SETS);
}

uint64_t compare_cache_bounds(cache_state c1, cache_state c2, uint64_t lower_bound, uint64_t upper_bound) {
  for (uint64_t set=lower_bound; set<upper_bound; set++) {
    for (uint64_t way=0; way<WAYS; way++) {
      cache_line * l1 = &c1[set][way];
      if (l1->valid) {
        // search a way in the second cache that has the same tag
        uint64_t found = 0;
        for (uint64_t way1=0; way1<WAYS; way1++) {
          cache_line * l2 = &c2[set][way1];
          if (l2->valid && (l1->tag == l2->tag))
            found = 1;
        }
        if (!found) {
          return l1->tag;
        }
      }
    }

    for (uint64_t way=0; way<WAYS; way++) {
      cache_line * l2 = &c2[set][way];
      if (l2->valid) {
        // search a way in the first cache that has the same tag
        uint64_t found = 0;
        for (uint64_t way1=0; way1<WAYS; way1++) {
          cache_line * l1 = &c1[set][way1];
          if (l1->valid && (l1->tag == l2->tag))
            found = 1;
        }
        if (!found)
          return l2->tag;
      }
    }
  }
  return 0;
}

uint64_t compare_cache_num_bounds(cache_state c1, cache_state c2, uint64_t lower_bound, uint64_t upper_bound) {
  for (uint64_t set=lower_bound; set<upper_bound; set++) {
    uint64_t num1 = 0;
    uint64_t num2 = 0;

    for (uint64_t way=0; way<WAYS; way++) {
      cache_line * l1 = &c1[set][way];
      if (l1->valid) {
        num1++;
      }
      cache_line * l2 = &c2[set][way];
      if (l2->valid) {
        num2++;
      }
    }

    if (num1 != num2) {
      return set;
    }
  }

  return 0;
}
