#include <stdint.h>

#ifdef BAREMETAL

int64_t add_reg (int64_t x, int64_t y) {
  register int64_t lx asm ("a0") = x;
  register int64_t ly asm ("a1") = y;
  register int64_t oldx asm ("a2") = x;
  register int64_t oldy asm ("a3") = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}

#else

int64_t add_reg (int64_t x, int64_t y) {
  int64_t lx = x;
  int64_t ly = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}

#endif

