#include <stdint.h>

void swap(uint64_t * x, uint64_t * y) {
  uint64_t a, b;
  a = * x;
  b = * y;
  if (a == b)
    return;
  * x = b;
  * y = a;
}

int main(void) {
  uint64_t a = 1;
  uint64_t b = 0;
  swap(&a, &b);
  return a;
}
