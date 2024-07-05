#include <stdint.h>

uint64_t mod2(uint64_t * i) {
  uint64_t j;
  j =  * i % 2;
  return j;
}

int main(void) {
  uint64_t j;
  j = 10;
  return mod2(&j);
}
