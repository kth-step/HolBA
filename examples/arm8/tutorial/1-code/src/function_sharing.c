#include <stdint.h>
#include "examples.h"

int64_t add(int64_t x, int64_t y) {
  return x + y;
}

int64_t add_times_two(int64_t x, int64_t y) {
  int64_t z = add(x, y);
  return add(z, z);
}

int64_t add_rec(int64_t x, int64_t y) {
  if (x == 0)
    return y;
  else if (x < 0)
    return -add_rec(-x, -y);
  else
    return add_rec(x - 1, y + 1);
}

int64_t add_rec_times_two(int64_t x, int64_t y) {
  int64_t z = add_rec(x, y);
  return add_rec(z, z);
}

int64_t add_reg_fast(int64_t x, int64_t y) {
  if (x < 0)
    return -add_reg(-x, -y);
  else
    return add_reg(x, y);
}

int64_t add_reg_fast_times_two(int64_t x, int64_t y) {
  int64_t z = add_reg_fast(x, y);
  return add_reg_fast(z, z);
}


