#include "config.h"

// this is the abstraction module for the low level assembly code exp_cache_run_asm.S

#ifdef RUN_CACHE

#if !defined(__has_include)
#  error "need __has_include"
#endif

#if !__has_include("experiment/asm_setup_1.h")
#  error "need at least asm code to setup state 1"
#endif

#if __has_include("experiment/asm_setup_train.h")
#  define EXP_HAS_INPUT_TRAIN
#endif

#if __has_include("experiment/asm_setup_2.h")
#  define EXP_HAS_INPUT_2
#endif

#include "cache.h"
#include <stdint.h>

uint64_t expmem_byte_to_word(uint8_t v) {
  uint64_t w = v;
  return ((w << 56) | (w << 48) | (w << 40) | (w << 32) |
          (w << 24) | (w << 16) | (w << 8 ) | (w << 0 ));
}

// memory space allocated for experiments
extern uint64_t _experiment_memory[32 * 1024 * 8 / 8];
void _clean_experiment_memory(uint64_t default_val) {
  int length = sizeof(_experiment_memory)/sizeof(uint64_t);
  for (int i = 0; i < length; i++) {
    _experiment_memory[i] = default_val;
  }
}

#ifdef EXP_HAS_INPUT_TRAIN
void _clean_experiment_memory_train() {
  _clean_experiment_memory(EXPMEM_TRAIN_DEFAULT_VALUE);
}
#endif

void _clean_experiment_memory_run1() {
  _clean_experiment_memory(EXPMEM_1_DEFAULT_VALUE);
}

#ifdef EXP_HAS_INPUT_2
void _clean_experiment_memory_run2() {
  _clean_experiment_memory(EXPMEM_2_DEFAULT_VALUE);
}
#endif

void _scamv_train();
void _scamv_run1();
void _scamv_run2();

void _cache_run(cache_state cache, void (*_clean_mem_run)(), void (*_scamv_run)(), void (*_clean_mem_train)(), void (*_scamv_train)());

static cache_state cache_temp;
uint8_t cache_run_mult_compare(uint8_t _input_id, cache_state cache_, uint8_t n) {
  void (*_clean_mem_run)()   = 0;
  void (*_scamv_run__)()     = 0;
  void (*_clean_mem_train)() = 0;
  void (*_scamv_train__)()   = 0;

#ifdef EXP_HAS_INPUT_TRAIN
  _clean_mem_train = _clean_experiment_memory_train;
  _scamv_train__   = _scamv_train;
#endif

  switch (_input_id) {
    case 1:
      _clean_mem_run = _clean_experiment_memory_run1;
      _scamv_run__   = _scamv_run1;
      break;
#ifdef EXP_HAS_INPUT_2
    case 2:
      _clean_mem_run = _clean_experiment_memory_run2;
      _scamv_run__   = _scamv_run2;
      break;
#endif
    default:
      while (1);
  }

  uint8_t diff = 0;
  _cache_run(cache_, _clean_mem_run, _scamv_run__, _clean_mem_train, _scamv_train__);
  for (uint8_t i = n; i > 0; i--) {
    _cache_run(cache_temp, _clean_mem_run, _scamv_run__, _clean_mem_train, _scamv_train__);
    if (compare_cache(cache_, cache_temp) != 0)
      diff++;
  }
  return diff;
}


#endif // RUN_CACHE

