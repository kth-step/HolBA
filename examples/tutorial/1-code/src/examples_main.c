#include <stdint.h>
#include "examples_main.h"
#include "examples.h"

#ifdef BAREMETAL
void _exit() {}
#endif // BAREMETAL

int main(int argc, char ** argv) {
  PRINTF(("=========================\n"));
  PRINTF(("first examples\n"));
  PRINTF(("=========================\n"));
  PRINTF(("CGD 6 9 %ld\n", gcd(6, 9)));
  PRINTF(("CGD 12 18 %ld\n", gcd(12, 18)));
  for (int i=0; i<20; i++) {
    PRINTF(("SQRT %d %ld\n", i, sqrt_(i)));
  }
  PRINTF(("POW MOD 3^3 mod 4 = 27 mod 4 = 3 ? %ld\n", modular_pow(3, 3, 4)));

  uint64_t buffer[255];
  buffer[0] = 0; buffer[1] = 10;
  buffer[0] = buffer[0]; // code to avoid compiler warning "varibale unused"
  // binary_search_buggy(buffer, 2, 1);
  PRINTF(("SEARCH 0 = %ld\n", binary_search_buggy(buffer, 2, 0)));
  for (int i=0; i<255; i++) {
    buffer[i] = i;
  }
  // PRINTF(("SEARCH 200 = %ld\n", binary_search_buggy2(buffer, 255, 200)));
  PRINTF(("SEARCH 200 = %ld\n", binary_search_ok2(buffer, 255, 200)));

  PRINTF(("=========================\n"));
  PRINTF(("main tutorial example\n"));
  PRINTF(("=========================\n"));
  PRINTF(("5 +   3  = %li\n", add_reg(5, 3)));
  PRINTF(("0 + (-3) = %li\n", add_reg(0,-3)));
  PRINTF(("5 + (-3) = %li\n", add_reg(5,-3)));
  
  return 0;
}


