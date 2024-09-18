#include <stdint.h>

void ifelse(uint64_t *x,uint64_t *k,uint32_t kbits)
{
  uint64_t *constants;
  *x += 1;
  *x += 2;
  *x += 3;
  if (kbits == 256) {
    constants = k;
  } else {
    constants = k + 4;
    *x += 8;
  }
  *x += 1;
  *x += 2;
  *x += *constants;
  *x += *constants;
}

/*
uint64_t ifelse(uint64_t *i, uint64_t j) {
  uint64_t ret;
  *i += 3;
  if (j == 256) {
    i += 16;
    ret = 0;
  } else {    
    ret = 1;
  }
  ret += 4334;
  ret -= 345;
  return ret;
}
*/

int main(void) {
  uint64_t i = 43434334;
  uint64_t a = 0;
  ifelse(&i, &a, 256);
  return 0;
}
