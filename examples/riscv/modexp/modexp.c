#include <stdint.h>

/*
void main(void) {
}
*/

uint32_t modexp(uint32_t e, uint32_t b, uint32_t m) {
  uint32_t r = 1;
  for (int i = 0; i < 32; i++) {
    if (e & (0x1 << i)) {
      r = (r * b) % m;
    }
    b = (b * b) % m;
  }
  return r;
}

