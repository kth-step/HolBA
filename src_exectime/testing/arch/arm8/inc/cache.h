#ifndef _CACHE_H
#define _CACHE_H

#include "config.h"
#include <stdint.h>

#ifndef CORTEX_A72
  //general: rpi3...
  #define WAYS (4)
  #define SETS (32 * 1024 / 64 / WAYS)
  #define SET(x) ((((uint64_t)(x))/64)%SETS)
  #define TAG_OF_ADDR(x) (((uint64_t)(x)) / SETS / 64)
  #define TAG_SET_TO_ADDR(tag, set) (tag * 64 * SETS + set*64)

  #define WAYS_L2 (16)
  #define SETS_L2 (512 * 1024 / 64 / WAYS_L2)
#else
  //rpi4
  #define WAYS (2)
  #define SETS (32 * 1024 / 64 / WAYS)
  #define SET(x) ((((uint64_t)(x))/64)%SETS)
  #define TAG_OF_ADDR(x) (((uint64_t)(x)) / SETS / 64)
  #define TAG_SET_TO_ADDR(tag, set) (tag * 64 * SETS + set*64)

  #define WAYS_L2 (16)
  // size of L2 is 1MB. Source: https://www.raspberrypi.org/documentation/hardware/raspberrypi/bcm2711/README.md
  #define SETS_L2 (1024 * 1024 / 64 / WAYS_L2)
#endif

#define TRUE (1)
#define FALSE (0)

typedef struct cache_line_ {
  uint64_t data[8];
  uint64_t tag;
  _Bool valid;
  uint64_t r0;
  uint64_t r1;
} cache_line;

typedef cache_line set_t[WAYS];
typedef set_t cache_state[SETS];

typedef struct prefetch_conf_ {
  uint8_t NPFSTRM; // Number of independent data prefetch streams
  _Bool STRIDE;    // sequence length that triggers data prefetch streams
  uint8_t L1PCTL;  // L1 Data prefetch control
} prefetch_conf;
uint64_t get_prefetching_conf();
prefetch_conf parse_prefetch_conf(uint64_t conf);
uint64_t set_prefetching_conf(uint64_t conf, prefetch_conf new_conf);


void flush_d_cache(uint64_t level);
void get_cache_line(cache_line *line, uint64_t set, uint64_t way);
void save_cache_state(cache_state cache);
void debug_line(cache_line * line, _Bool values);
void debug_set(set_t set, _Bool values);

void debug_line_info(cache_line * line);
void debug_set_info(set_t set);

void print_cache_full(cache_state c);
void print_cache_valid(cache_state c);

cache_line * get_line_for_pa(cache_state cache, uint64_t pa);
int hit_for_pa(cache_state cache, uint64_t pa);
uint64_t compare_cache(cache_state c1, cache_state c2);
uint64_t compare_cache_bounds(cache_state c1, cache_state c2, uint64_t lower_bound, uint64_t upper_bound);
uint64_t compare_cache_num_bounds(cache_state c1, cache_state c2, uint64_t lower_bound, uint64_t upper_bound);

#endif
