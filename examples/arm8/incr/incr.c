#include <stdint.h>

uint64_t incr(uint64_t i) {
  return i + 1;
}

int main(void) {
  uint64_t i = incr(0);
  return i;
}
