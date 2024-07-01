#include <stdint.h>

uint8_t storestorestore_loadload(uint64_t x, uint64_t* y, uint8_t* z) {
  *y = x + 3;
  *z = (uint8_t)(x + 5);
  x = *y + 2;
  return *z;
}

int main(void) {
  return storestorestore_loadload(23, (uint64_t*)0x1000000, (uint8_t*)0x2000000);
}

