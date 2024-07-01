#include <stdint.h>

void main(void) {
  storestorestore_loadload(23, 0x1000000, 0x2000000);
}

uint8_t storestorestore_loadload(uint64_t x, uint64_t* y, uint8_t* z) {
  *y = x + 3;
  *z = (uint8_t)(x + 5);
  x = *y + 2;
  return *z;
}

