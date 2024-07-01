#include <stdint.h>

uint8_t storestorestore_loadload(uint64_t x, uint64_t* y, uint8_t* z) {
  *y = x + 3;
  *z = (uint8_t)(x + 5);
  x = *y + 2;
  return *z;
}

#define GEN_ADDR(x) (0xFFFFFFFF00000000 + (0x10 * x))

int main(void) {
  return storestorestore_loadload(23, (uint64_t*)GEN_ADDR(0), (uint8_t*)GEN_ADDR(1));
}

