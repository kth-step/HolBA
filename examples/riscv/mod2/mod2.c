#include <stdint.h>

uint64_t mod2(uint64_t i) {
  return i % 2;
}

int main(void) {
  return mod2(10); 
}
