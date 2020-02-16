#ifndef _EXAMPLES_MAIN_H
#define _EXAMPLES_MAIN_H


#ifdef BAREMETAL
  #define PRINTF(x) (void)0
#else
  #include <stdio.h>
  #define PRINTF(x) printf x
#endif // BAREMETAL


#endif // _EXAMPLES_MAIN_H
