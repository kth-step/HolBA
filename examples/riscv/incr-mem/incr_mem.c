#include <stdint.h>

void incr(uint64_t *i) {
  *i = *i + 1;
}

int main(void) {
  uint64_t j = 0;
  incr(&j);
  return j;
}
