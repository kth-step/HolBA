#include <stdint.h>

// example from wikipedia, adjusted (is_even and is_odd)
uint64_t is_odd(uint64_t n);

uint64_t is_even(uint64_t n) {
  if (n == 0)
    return 1;
  else
    return is_odd(n - 1);
}

uint64_t is_odd(uint64_t n) {
  return !is_even(n);
}


