#include <stdint.h>

#ifdef BAREMETAL
  #define PRINTF(x) (void)0

void _exit() {}

#else
  #include <stdio.h>
  #define PRINTF(x) printf x
#endif

int64_t sqrt_(int64_t x) {
  uint64_t y = 0;
  while ((y+1)*(y+1) < x) {
    y += 1;
  }
  return y;
}


int main(int argc, char ** argv) {
  
  for (int i=0; i<20; i++) {
    PRINTF(("SQRT %d %ld\n", i, sqrt_(i)));
  }

  return 0;
}
