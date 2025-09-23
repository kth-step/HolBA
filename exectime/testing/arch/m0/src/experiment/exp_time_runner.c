#include "config.h"

// this is the abstraction module for the low level assembly code exp_cache_run_asm.S

#ifdef RUN_TIME


#include <stdint.h>

uint32_t expmem_byte_to_word(uint8_t v) {
  uint32_t w = v;
  return ((w << 24) | (w << 16) | (w << 8 ) | (w << 0 ));
}

// memory space allocated for experiments
uint32_t _experiment_memory[1024/4];
void _clean_experiment_memory() {
  uint32_t default_val = 0;
  int length = sizeof(_experiment_memory)/sizeof(uint64_t);
  for (int i = 0; i < length; i++) {
    _experiment_memory[i] = default_val;
  }
}

void _time_run1();
void _time_run2();
uint32_t _time_run(void (*_time_run_)());

uint32_t time_run(uint8_t _input_id) {
  void (*_time_run__)()     = 0;

  switch (_input_id) {
    case 1:
      _time_run__   = _time_run1;
      break;
#ifdef RUN_2EXPS
    case 2:
      _time_run__   = _time_run2;
      break;
#endif
    default:
      while (1);
  }

  return _time_run(_time_run__);
}


#endif // RUN_TIME

