#include "config.h"

#ifdef RUN_CACHE

#include "lib/printf.h"
#include "mmu.h"
#include "cache.h"

#define __UNUSED __attribute__((unused))
#define __ALIGN(x) __attribute__ ((aligned (x)))
#define PAGE_SIZE (4096)
/* page table memory */
uint64_t page_table_l1[4] __ALIGN(PAGE_SIZE);


static void __UNUSED basic_mmu() {
  init_mmu();
  set_l1(page_table_l1);
  // Set up translation table entries in memory with looped store
  // instructions.
  // Set the level 1 translation table.
  l1_set_translation(page_table_l1, 0, 0, 0);
  l1_set_translation(page_table_l1, 0x40000000, 0, 0);
  // Executable Inner and Outer Shareable.
  // R/W at all ELs secure memory
  // AttrIdx=000 Device-nGnRnE.
  // The third entry is 1GB block from 0x80000000 to 0xBFFFFFFF.
  l1_set_translation(page_table_l1, 0x80000000, 0, 1);
  //l1_set_translation(page_table_l1, 0xC0000000, 0, 1);

  // TODO: dirty quick fix for rpi4, overwrites the last mapping, second cacheable alias
  l1_set_translation(page_table_l1, 0xC0000000, 0xC0000000, 0);
  
  enable_mmu();
}



#define CACHEABLE(x) ((void *)(((uint64_t)(&x)) + 0x80000000))
#define ALIAS(x)     ((void *)(((uint64_t)(&x)) + 0x40000000))



void assert(uint64_t condition, char * string) {
  if (condition)
    printf("condition %s holds\n", string);
  else
    printf("condition %s fails\n", string);
}


static cache_state cache1;
static cache_state cache2;


void test_mmu_alias() {
  flush_d_cache(0);
  flush_d_cache(1);
  // check memory alias
  volatile uint64_t x = 0;
  x = 0x64;
  printf("x is in %x\n", &x);
  uint64_t * new_ptr = (uint64_t*)(ALIAS(x));

  assert((x == (*new_ptr)), " uncacheable alias has the same value");
  
  // access a cacheable value
  volatile uint64_t y = 0;
  y = *((uint64_t * )CACHEABLE(x));
  assert((x == y), " cacheable alias has the same value");
}

void test_value_in_cache() {
  // check memory alias
  volatile uint64_t x = 0;

  flush_d_cache(0);
  flush_d_cache(1);

  x = 0x41;
  printf("x is in %x and value is %x\n", &x, x);
  // access a cacheable value
  volatile uint64_t * yP = (uint64_t * )CACHEABLE(x);
  volatile uint64_t y = 0;
  y = *(yP);
  printf("y is in %x and value is %x\n", yP, y);
  assert((x == y), " cacheable alias has the same value");

  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(x))], TRUE);
  assert(hit_for_pa(cache1, (uint64_t)(&x)), " x is in the cache");

}

void test_cache_flush() {
  // check memory alias
  volatile uint64_t x = 0;
  flush_d_cache(0);
  flush_d_cache(1);

  x = 0x42;
  printf("x is in %x and value is %x\n", &x, x);
  // access a cacheable value
  volatile uint64_t * yP = (uint64_t * )CACHEABLE(x);
  volatile uint64_t y = 0;
  y = *(yP);
  printf("y is in %x and value is %x\n", yP, y);
  assert((x == y), " cacheable alias has the same value");

  x = 0x43;
  y = *(yP);
  printf("y is in %x and value is %x\n", yP, y);
  assert((x != y), " cacheable alias differs");

  printf("-------------------- CACHE FLUSH --------------------\n");
  flush_d_cache(0);
  flush_d_cache(1);


  y = *(yP);
  printf("y is in %x and value is %x\n", yP, y);
  assert((x == y), " cacheable alias has the same value");
}

extern uint64_t _experiment_memory[32 * 1024 * 8 / 8];
#define memory _experiment_memory

void test_two_ways() {
  flush_d_cache(0);
  flush_d_cache(1);
  uint64_t a1 = 0;
  uint64_t a2 = a1 + 32 * 1024 * 1 / 8;

  memory[a1] = 0x123;
  memory[a2] = 0x456;
  
  volatile uint64_t * xP = (uint64_t * )CACHEABLE(memory[a1]);
  printf("addresses %x %x %x \n", &(memory[a1]), &(memory[a2]), xP);
  volatile uint64_t x = *(xP);
  volatile uint64_t * yP = (uint64_t * )CACHEABLE(memory[a2]);
  volatile uint64_t y = *(yP);

  printf("values %x %x\n", x, y);

  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[a1]))], TRUE);
  assert(hit_for_pa(cache1, (uint64_t)(&memory[a1])), " a1 is in the cache");
  assert(hit_for_pa(cache1, (uint64_t)(&memory[a2])), " a2 is in the cache");
}


void test_clean_replacement() {
  flush_d_cache(0);
  flush_d_cache(1);
  uint64_t a1 = 0;
  uint64_t a2 = a1 + 32 * 1024 * 1 / 8;
  uint64_t a3 = a1 + 32 * 1024 * 2 / 8;

  memory[a1] = 0x123;
  memory[a2] = 0x456;
  memory[a3] = 0x789;
  
  volatile uint64_t * xP = (uint64_t * )CACHEABLE(memory[a1]);
  volatile uint64_t x __UNUSED = *(xP);
  volatile uint64_t * yP = (uint64_t * )CACHEABLE(memory[a2]);
  volatile uint64_t y __UNUSED = *(yP);

  flush_d_cache(0);
  flush_d_cache(1);

  volatile uint64_t * zP = (uint64_t * )CACHEABLE(memory[a3]);
  volatile uint64_t z __UNUSED = *(zP);

  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[a1]))], TRUE);
}

void test_replacement() {
  flush_d_cache(0);
  flush_d_cache(1);
  uint64_t a1 = 0;
  uint64_t a2;
  volatile uint64_t * xP;
  volatile uint64_t x __UNUSED;
  int i;
  printf("address of a1 %x\n", &memory[a1]);
  for (i=0; i<4; i++) {
    a2 = a1 + 32 * 1024 * (i) / 8;
    memory[a2] = 0x120 + i;
    xP = (uint64_t * )CACHEABLE(memory[a2]);
    x = *(xP);
  }
  a2 = a1 + 32 * 1024 * (0) / 8;
  xP = (uint64_t * )CACHEABLE(memory[a2]);
  x = *(xP);
  
  /* printf("-------------------- DEBUG CACHE --------------------\n"); */
  /* save_cache_state(cache1); */
  /* debug_set(cache1[SET(CACHEABLE(memory[a1]))]); */

  for (i=0; i<2; i++) {
    a2 = a1 + 32 * 1024 * (i+4) / 8;
    memory[a2] = 0x120 + i;
    xP = (uint64_t * )CACHEABLE(memory[a2]);
    x = *(xP);
    /* printf("-------------------- DEBUG CACHE --------------------\n"); */
    /* save_cache_state(cache1); */
    /* debug_set(cache1[SET(CACHEABLE(memory[a1]))]); */
  }

  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[a1]))], TRUE);
}

#define COLLISION_IDX_OFFSET (32 * 1024 / 8)
#define LINE_IDX_OFFSET (64/8)

static void entropy_code(uint64_t x1, uint64_t x2, uint64_t x3) {
  if (x2 > x3) {
    x1 = x2 + x3;
  }
  volatile uint64_t v __UNUSED = 0;
  v = *((uint64_t *)x1);
}

static void __UNUSED test_entropy() {
  flush_d_cache(0);
  flush_d_cache(1);
  memory[0] = 0x100;
  entropy_code((uint64_t)CACHEABLE(memory[0]), 0, 0);
  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[0]))], TRUE);
  assert(hit_for_pa(cache1, (uint64_t)(&memory[0])), " 0 is in the cache");
  assert(!(hit_for_pa(cache1, (uint64_t)(&memory[COLLISION_IDX_OFFSET]))), " COLLISION is not the cache");
  assert(!(hit_for_pa(cache1, (uint64_t)(&memory[LINE_IDX_OFFSET]))), " NEXT line is not the cache");

  flush_d_cache(0);
  flush_d_cache(1);
  
  entropy_code((uint64_t)CACHEABLE(memory[0]), (uint64_t)CACHEABLE(memory[2*LINE_IDX_OFFSET]), LINE_IDX_OFFSET*8);
  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[3*LINE_IDX_OFFSET]))], TRUE);
  assert(hit_for_pa(cache1, (uint64_t)(&memory[3*LINE_IDX_OFFSET])), " line 4 is in the cache");
  assert(!(hit_for_pa(cache1, (uint64_t)(&memory[LINE_IDX_OFFSET]))), " line 0 is not it the cahce");
}


void test_entropy_pair(uint64_t x1, uint64_t x2, uint64_t x3, uint64_t pa,
                       uint64_t x11, uint64_t x21, uint64_t x31, uint64_t pa1,
                       uint64_t eq
                       ) {
  flush_d_cache(0);
  flush_d_cache(1);
  entropy_code(x1, x2, x3);
  save_cache_state(cache1);
  assert(hit_for_pa(cache1, pa), " 0 is in the cache");

  flush_d_cache(0);
  flush_d_cache(1);
  entropy_code(x11, x21, x31);
  save_cache_state(cache2);
  assert(hit_for_pa(cache2, pa1), " 0 is in the cache");

  assert((compare_cache(cache1, cache2) == 0) == (eq == 0), " indistinguishable caches");
}

void test_entropy_pair_1_1() {
  test_entropy_pair((uint64_t)CACHEABLE(memory[0]), 100, 200, (uint64_t)(&memory[0]),
                    (uint64_t)CACHEABLE(memory[2]), 58, 64, (uint64_t)(&memory[2]),
                    0
                    );

  test_entropy_pair((uint64_t)CACHEABLE(memory[3*LINE_IDX_OFFSET]), 100, 200, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    (uint64_t)CACHEABLE(memory[2]), (uint64_t)CACHEABLE(memory[2*LINE_IDX_OFFSET]), LINE_IDX_OFFSET*8+8, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    0
                    );

  test_entropy_pair((uint64_t)CACHEABLE(memory[LINE_IDX_OFFSET]), (uint64_t)CACHEABLE(memory[3*LINE_IDX_OFFSET]), 0, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    (uint64_t)CACHEABLE(memory[2]), (uint64_t)CACHEABLE(memory[2*LINE_IDX_OFFSET]), LINE_IDX_OFFSET*8+8, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    0
                    );

  test_entropy_pair((uint64_t)CACHEABLE(memory[0]), 100, 200, (uint64_t)(&memory[0]),
                    (uint64_t)CACHEABLE(memory[LINE_IDX_OFFSET]), 58, 64, (uint64_t)(&memory[LINE_IDX_OFFSET]),
                    1
                    );

  test_entropy_pair((uint64_t)CACHEABLE(memory[3*LINE_IDX_OFFSET + COLLISION_IDX_OFFSET]), 100, 200, (uint64_t)(&memory[3*LINE_IDX_OFFSET +  COLLISION_IDX_OFFSET]),
                    (uint64_t)CACHEABLE(memory[2]), (uint64_t)CACHEABLE(memory[2*LINE_IDX_OFFSET]), LINE_IDX_OFFSET*8+8, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    1
                    );

  test_entropy_pair((uint64_t)CACHEABLE(memory[LINE_IDX_OFFSET]), (uint64_t)CACHEABLE(memory[4*LINE_IDX_OFFSET]), 0, (uint64_t)(&memory[4*LINE_IDX_OFFSET]),
                    (uint64_t)CACHEABLE(memory[2]), (uint64_t)CACHEABLE(memory[2*LINE_IDX_OFFSET]), LINE_IDX_OFFSET*8+8, (uint64_t)(&memory[3*LINE_IDX_OFFSET]),
                    1
                    );
}


void access_set_0(int i)
{
  uint64_t a1 = 0;
  uint64_t a2;
  volatile uint64_t * xP;
  volatile uint64_t x __UNUSED;

  a2 = a1 + 32 * 1024 * (i) / 8;
  printf("access set 0 with idx %d = %x\n", i, &memory[a2]);

  memory[a2] = 0x120 + i;
  xP = (uint64_t * )CACHEABLE(memory[a2]);
  x = *(xP);
}

void print_cache_set_0()
{
  save_cache_state(cache1);
  debug_set(cache1[SET(CACHEABLE(memory[0]))], TRUE);
}

int8_t sequence1[] = {
  0,
  1,
  2,
  3,
  4,
  -1,
  -1,
  -1,
  -1,
  -1,
};
int8_t sequence2[] = {
  2,
  3,
  -1,
  -1,
  -1,
  -1,
  -1,
  -1,
  -1,
  -1,
};
void access_sequence()
{
  int i;

  access_set_0(0);

  printf("flushing cache..\n");
  flush_d_cache(0);
  flush_d_cache(1);

  printf("\n");
  for(i = 0; i < 10; i++)
  {
    int8_t idx = sequence1[i];
    if (idx < 0) {
      break;
    } else {
      access_set_0(idx);
    }
  }

  printf("\n");
  print_cache_set_0();

  printf("\n");
  for(i = 0; i < 10; i++)
  {
    int8_t idx = sequence2[i];
    if (idx < 0) {
      break;
    } else {
      access_set_0(idx);
    }
  }
  printf("\n");
  print_cache_set_0();
  access_set_0(6);
  access_set_0(5);

  printf("\n");

  print_cache_set_0();
}

void test_prefetching(void) {
  uint64_t value = get_prefetching_conf();
  prefetch_conf conf = parse_prefetch_conf(value);
  printf("Conf for prefetching 1 %x\n", value);
  printf("NPFSTRM %d\n", conf.NPFSTRM);
  printf("STRIDE %d\n", conf.STRIDE);
  printf("L1PCTL %d\n", conf.L1PCTL);

  conf.NPFSTRM = 1;
  conf.STRIDE = 0;
  conf.L1PCTL = 5;
  value = set_prefetching_conf(value, conf);
  printf("New value is %x\n", value);

  value = get_prefetching_conf();
  conf = parse_prefetch_conf(value);
  printf("Conf for prefetching 2 %x\n", value);
  printf("NPFSTRM %d\n", conf.NPFSTRM);
  printf("STRIDE %d\n", conf.STRIDE);
  printf("L1PCTL %d\n", conf.L1PCTL);


  uint64_t a1 = 0;
  uint64_t iset = 0;
  flush_d_cache(0);
  flush_d_cache(1);

  save_cache_state(cache1);
  //debug_set(cache1[SET(CACHEABLE(memory[a1]))], FALSE);
  for (iset=0; iset<10; iset++) {
    debug_set_info(cache1[SET(CACHEABLE(memory[a1])) + iset]);
  }


  memory[a1] = 42;
  volatile uint64_t * xP = (uint64_t * )CACHEABLE(memory[a1]);
  uint64_t tag = TAG_OF_ADDR(xP);
  uint64_t set = SET(xP);
  
  volatile uint64_t x = *(xP);
  /* cause a prefetching of three lines */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* does not cause a prefetching */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+3))); */
  /* Triggers */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+4))); */
  /* No trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* No trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+3))); */
  /* trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+3))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+6))); */
  /* trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+4))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+8))); */
  /* no trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+5))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+10))); */
  /* Triggers */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+4))); */
  /* also triggers */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2)+ 6)); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+4))); */
  /* Does not triggers */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1+SETS))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2+2*SETS))); */
  /* Does not trigger */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* flush_d_cache(0); */
  /* flush_d_cache(1); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* prefetch many lines */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+3))); */
  /* x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+4))); */

  /* Does not prefetch the second sequence */
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+1)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+2)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+3)));
  for (iset=0; iset<1000000; iset++) {
    x +=1;
  }
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+10)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+11)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+12)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+13)));
  x += *((uint64_t*)(TAG_SET_TO_ADDR(tag, set+14)));

  //Cortex-A53 has PMU event 0xC2 "Linefill because of prefetch" which might help diagnose (see Events).
  // http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.ddi0500j/BIIDBAFB.html
  
  printf("values %d\n", x);

  save_cache_state(cache1);
  //debug_set(cache1[SET(CACHEABLE(memory[a1]))], FALSE);
  for (iset=0; iset<50; iset++) {
    printf("%d > ", iset);
    debug_set_info(cache1[SET(CACHEABLE(memory[a1])) + iset]);
  }
}

#ifdef SINGLE_EXPERIMENTS
void run_cache_experiment()
{
  basic_mmu();
  /* printf("-------------------- ACCESS SEQ --------------------\n"); */
  /* access_sequence(); */
  /* printf("-------------------- START TEST 1 --------------------\n"); */
  /* test_mmu_alias(); */
  /* printf("-------------------- START TEST 2 --------------------\n"); */
  /* test_value_in_cache(); */
  /* printf("-------------------- START TEST 3 --------------------\n"); */
  /* test_cache_flush(); */
  /* printf("-------------------- START TEST 4 --------------------\n"); */
  /* test_two_ways(); */
  /* printf("-------------------- START TEST 5 --------------------\n"); */
  /* test_clean_replacement(); */
  /* printf("-------------------- START TEST 6 --------------------\n"); */
  /* test_replacement(); */
  /* printf("-------------------- START TEST 7 --------------------\n"); */
  /* test_replacement(); */
  /* test_entropy(); */ 
  /* test_entropy_pair_1_1(); */

  test_prefetching();
}

#endif // SINGLE_EXPERIMENTS

#endif // RUN_CACHE
