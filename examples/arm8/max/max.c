#include <stdint.h>

uint64_t max(uint64_t x, uint64_t y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
}

int main(void) {
  uint64_t a = 5;
  uint64_t b = 7;
  return max(a, b);
}
