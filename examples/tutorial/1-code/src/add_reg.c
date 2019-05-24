#include <stdint.h>

#ifdef BAREMETAL

int64_t add_reg (int64_t x, int64_t y) {
  register int64_t lx asm ("x2") = x;
  register int64_t ly asm ("x3") = y;
  register int64_t oldx asm ("x4") = x;
  register int64_t oldy asm ("x5") = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}

#endif


