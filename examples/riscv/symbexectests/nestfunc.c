#include <stdint.h>

uint32_t nested(uint64_t a, uint32_t b) {
  return a + b
}

/*
uint32_t outer(uint64_t x, uint32_t y) {
  uint32_t r = 1;
  r += nested(x, y);
  return r;
}
*/

void main(void) {
  uint32_t r = 1;
  r += nested(3, 7);
}
