#include "config.h"

#ifdef RUN_CACHE


#include <stdint.h>
#define CACHEABLE(x) ((void *)(((uint64_t)(x)) + 0x80000000))

// memory space allocated for experiments
extern uint64_t _experiment_memory[32 * 1024 * 8 / 8];
//NOTE: already defined in ./arch/arm8/src/experiment/exp_cache_runner.c
/*void _clean_experiment_memory() {
  int length = sizeof(_experiment_memory)/sizeof(uint64_t);
  for (int i = 0; i < length; i++) {
    _experiment_memory[i] = 0;
  }
}*/

void _zero_experiment_cache() {
  int length = sizeof(_experiment_memory)/sizeof(uint64_t);
  for (int i = 0; i < length; i++) {
  	 // access a cacheable value
  	  volatile uint64_t * yP = (uint64_t * )CACHEABLE(&_experiment_memory);
  	  yP[i] = 0;
  }
}

void _check_experiment_memory() {
  int length = sizeof(_experiment_memory)/sizeof(uint64_t);
  for (int i = 0; i < length; i++) {
  	 // access a cacheable value
  	  volatile uint64_t * yP = (uint64_t * )CACHEABLE(&_experiment_memory);
  	
  	  if (yP[i] != 0x00000000){ 	  	  
    	  	  printf("memory content at %x is %x \n", yP + i, yP[i]);
  	  }
  }
}

#endif // RUN_CACHE

