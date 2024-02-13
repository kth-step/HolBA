#include <stdint.h>

uint64_t isqrt(uint64_t x) {
  uint64_t y = 0;
  while ((y+1)*(y+1) <= x) {
    y += 1;
  }
  return y;
}
