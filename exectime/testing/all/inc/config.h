#ifndef CONFIG_H
#define CONFIG_H

#include "config_input.h"

#if   defined(__PROGPLAT_BOARD__RPI3) || defined(__PROGPLAT_BOARD__RPI4)
  #ifndef __PROGPLAT_ARCH__ARM8
    #error "wrong architecture for selected board type"
  #endif
  #ifdef __PROGPLAT_BOARD__RPI4
    #define CORTEX_A72
  #endif
#elif defined(__PROGPLAT_BOARD__RPI2)
  #ifndef __PROGPLAT_ARCH__ARM7
    #error "wrong architecture for selected board type"
  #endif
#elif defined __PROGPLAT_BOARD__LPC11C24
  #ifndef __PROGPLAT_ARCH__M0
    #error "wrong architecture for selected board type"
  #endif
#elif defined __PROGPLAT_BOARD__STM32F0
  #ifndef __PROGPLAT_ARCH__M0
    #error "wrong architecture for selected board type"
  #endif
#elif defined __PROGPLAT_BOARD__ARTY_A7_100T__FE310
  #ifndef __PROGPLAT_ARCH__RV32IMAC
    #error "wrong architecture for selected board type"
  #endif
#else
  #error "no known board type selected"
#endif

#ifdef __PROGPLAT_TYPE__EXPS2
  #define RUN_2EXPS
#elif defined __PROGPLAT_TYPE__EXPS1
  #define RUN_1EXPS
#else
  #error "no experiment type selected"
#endif

#ifdef __PROGPLAT_PARAMS__CACHE_MULTIW
  #define RUN_CACHE
  #define RUN_CACHE_MULTIW
#elif defined __PROGPLAT_PARAMS__CACHE_MULTIW_NUMINSET
  #define RUN_CACHE
  #define RUN_CACHE_MULTIW_NUMINSET
#elif defined __PROGPLAT_PARAMS__CACHE_MULTIW_SUBSET
  #define RUN_CACHE
  #define RUN_CACHE_MULTIW_SUBSET
#elif defined __PROGPLAT_PARAMS__CACHE_MULTIW_SUBSET_PAGE_BOUNDARY
  #define RUN_CACHE
  #define RUN_CACHE_MULTIW_SUBSET_PAGE_BOUNDARY
#elif defined __PROGPLAT_PARAMS__TIME
  #define RUN_TIME
#elif defined __PROGPLAT_PARAMS__NOTHING
#else
  #error "no experiment parameters selected"
#endif

#ifdef __PROGPLAT_MUL_RUNS__
  #define NUM_MUL_RUNS __PROGPLAT_MUL_RUNS__
#else
  #define NUM_MUL_RUNS 10
#endif

#ifdef __PROGPLAT_MEM_DEF_1__
  #define EXPMEM_1_DEFAULT_VALUE __PROGPLAT_MEM_DEF_1__
#else
  #define EXPMEM_1_DEFAULT_VALUE 0
#endif

#ifdef __PROGPLAT_MEM_DEF_2__
  #define EXPMEM_2_DEFAULT_VALUE __PROGPLAT_MEM_DEF_2__
#else
  #define EXPMEM_2_DEFAULT_VALUE 0
#endif

#ifdef __PROGPLAT_MEM_DEF_TRAIN__
  #define EXPMEM_TRAIN_DEFAULT_VALUE __PROGPLAT_MEM_DEF_TRAIN__
#else
  #define EXPMEM_TRAIN_DEFAULT_VALUE 0
#endif

#endif // CONFIG_H

