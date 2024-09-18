#include <stdint.h>

static const char sigma[16] = "expand 32-byte k";
static const char tau[16] = "expand 16-byte k";

void ifelse(uint64_t *x,unsigned char *k,uint32_t kbits)
{
  const char *constants;
  *x += 1;
  *x += 2;
  *x += 3;
  if (kbits == 256) {
    constants = sigma;
  } else {
    constants = tau;
  }
  *x += 1;
  *x += 2;
  *x += *constants;
  *x += *constants;
}
int main(void) {
  uint64_t i = 43434334;
  unsigned char a = 0;
  ifelse(&i, &a, 256);
  return 0;
}
