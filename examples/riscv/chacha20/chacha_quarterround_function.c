/*
chacha-merged.c version 20080118
D. J. Bernstein
Public domain.
*/

#include "chacha.h"

#define U8C(v) (v##U)
#define U32C(v) (v##U)

#define U8V(v) ((unsigned char)(v) & U8C(0xFF))
#define U32V(v) ((uint32_t)(v) & U32C(0xFFFFFFFF))

#define ROTL32(v, n) \
  (U32V((v) << (n)) | ((v) >> (32 - (n))))

#if (USE_UNALIGNED == 1)
#define U8TO32_LITTLE(p) \
    (*((uint32_t *)(p)))
#define U32TO8_LITTLE(p, v) \
    do { \
      *((uint32_t *)(p)) = v; \
    } while (0)
#else
#define U8TO32_LITTLE(p) \
  (((uint32_t)((p)[0])      ) | \
   ((uint32_t)((p)[1]) <<  8) | \
   ((uint32_t)((p)[2]) << 16) | \
   ((uint32_t)((p)[3]) << 24))
#define U32TO8_LITTLE(p, v) \
  do { \
    (p)[0] = U8V((v)      ); \
    (p)[1] = U8V((v) >>  8); \
    (p)[2] = U8V((v) >> 16); \
    (p)[3] = U8V((v) >> 24); \
  } while (0)
#endif

#define ROTATE(v,c) (ROTL32(v,c))
#define XOR(v,w) ((v) ^ (w))
#define PLUS(v,w) (U32V((v) + (w)))
#define PLUSONE(v) (PLUS((v),1))

uint32_t QUARTERROUND(uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
  a = PLUS(a,b); d = ROTATE(XOR(d,a),16);
  c = PLUS(c,d); b = ROTATE(XOR(b,c),12);
  a = PLUS(a,b); d = ROTATE(XOR(d,a), 8);
  c = PLUS(c,d); b = ROTATE(XOR(b,c), 7);
  return a+b+c+d;
}

static const char sigma[16] = "expand 32-byte k";
static const char tau[16] = "expand 16-byte k";

void
chacha_keysetup(struct chacha_ctx *x,const unsigned char *k,uint32_t kbits)
{
  const char *constants;

  x->input[4] = U8TO32_LITTLE(k + 0);
  x->input[5] = U8TO32_LITTLE(k + 4);
  x->input[6] = U8TO32_LITTLE(k + 8);
  x->input[7] = U8TO32_LITTLE(k + 12);
  if (kbits == 256) { /* recommended */
    k += 16;
    constants = sigma;
  } else { /* kbits == 128 */
    constants = tau;
  }
  x->input[8] = U8TO32_LITTLE(k + 0);
  x->input[9] = U8TO32_LITTLE(k + 4);
  x->input[10] = U8TO32_LITTLE(k + 8);
  x->input[11] = U8TO32_LITTLE(k + 12);
  x->input[0] = U8TO32_LITTLE(constants + 0);
  x->input[1] = U8TO32_LITTLE(constants + 4);
  x->input[2] = U8TO32_LITTLE(constants + 8);
  x->input[3] = U8TO32_LITTLE(constants + 12);
}

void
chacha_ivsetup(struct chacha_ctx *x, const unsigned char *iv, const unsigned char *counter)
{
  x->input[12] = counter == NULL ? 0 : U8TO32_LITTLE(counter + 0);
  //x->input[13] = counter == NULL ? 0 : U8TO32_LITTLE(counter + 4);
  x->input[13] = U8TO32_LITTLE(iv + 0);
  x->input[14] = U8TO32_LITTLE(iv + 4);
  x->input[15] = U8TO32_LITTLE(iv + 8);
}

void
chacha_encrypt_bytes(struct chacha_ctx *x,const unsigned char *m,unsigned char *c,uint32_t bytes)
{
  uint32_t x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15;
  uint32_t j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15;
  unsigned char *ctarget = NULL;
  unsigned char tmp[64];
  u_int i;

  if (!bytes) return;

  j0 = x->input[0];
  j1 = x->input[1];
  j2 = x->input[2];
  j3 = x->input[3];
  j4 = x->input[4];
  j5 = x->input[5];
  j6 = x->input[6];
  j7 = x->input[7];
  j8 = x->input[8];
  j9 = x->input[9];
  j10 = x->input[10];
  j11 = x->input[11];
  j12 = x->input[12];
  j13 = x->input[13];
  j14 = x->input[14];
  j15 = x->input[15];

  for (;;) {
    if (bytes < 64) {
#if (USE_MEMCPY == 1)
      memcpy(tmp, m, bytes);
#else
      for (i = 0;i < bytes;++i) tmp[i] = m[i];
#endif
      m = tmp;
      ctarget = c;
      c = tmp;
    }
    x0 = j0;
    x1 = j1;
    x2 = j2;
    x3 = j3;
    x4 = j4;
    x5 = j5;
    x6 = j6;
    x7 = j7;
    x8 = j8;
    x9 = j9;
    x10 = j10;
    x11 = j11;
    x12 = j12;
    x13 = j13;
    x14 = j14;
    x15 = j15;
    for (i = 20;i > 0;i -= 2) {
      QUARTERROUND( x0, x4, x8,x12);
      QUARTERROUND( x1, x5, x9,x13);
      QUARTERROUND( x2, x6,x10,x14);
      QUARTERROUND( x3, x7,x11,x15);
      QUARTERROUND( x0, x5,x10,x15);
      QUARTERROUND( x1, x6,x11,x12);
      QUARTERROUND( x2, x7, x8,x13);
      QUARTERROUND( x3, x4, x9,x14);
    }
    x0 = PLUS(x0,j0);
    x1 = PLUS(x1,j1);
    x2 = PLUS(x2,j2);
    x3 = PLUS(x3,j3);
    x4 = PLUS(x4,j4);
    x5 = PLUS(x5,j5);
    x6 = PLUS(x6,j6);
    x7 = PLUS(x7,j7);
    x8 = PLUS(x8,j8);
    x9 = PLUS(x9,j9);
    x10 = PLUS(x10,j10);
    x11 = PLUS(x11,j11);
    x12 = PLUS(x12,j12);
    x13 = PLUS(x13,j13);
    x14 = PLUS(x14,j14);
    x15 = PLUS(x15,j15);

    x0 = XOR(x0,U8TO32_LITTLE(m + 0));
    x1 = XOR(x1,U8TO32_LITTLE(m + 4));
    x2 = XOR(x2,U8TO32_LITTLE(m + 8));
    x3 = XOR(x3,U8TO32_LITTLE(m + 12));
    x4 = XOR(x4,U8TO32_LITTLE(m + 16));
    x5 = XOR(x5,U8TO32_LITTLE(m + 20));
    x6 = XOR(x6,U8TO32_LITTLE(m + 24));
    x7 = XOR(x7,U8TO32_LITTLE(m + 28));
    x8 = XOR(x8,U8TO32_LITTLE(m + 32));
    x9 = XOR(x9,U8TO32_LITTLE(m + 36));
    x10 = XOR(x10,U8TO32_LITTLE(m + 40));
    x11 = XOR(x11,U8TO32_LITTLE(m + 44));
    x12 = XOR(x12,U8TO32_LITTLE(m + 48));
    x13 = XOR(x13,U8TO32_LITTLE(m + 52));
    x14 = XOR(x14,U8TO32_LITTLE(m + 56));
    x15 = XOR(x15,U8TO32_LITTLE(m + 60));

    j12 = PLUSONE(j12);
    if (!j12) {
      j13 = PLUSONE(j13);
      /* stopping at 2^70 bytes per nonce is user's responsibility */
    }

    U32TO8_LITTLE(c + 0,x0);
    U32TO8_LITTLE(c + 4,x1);
    U32TO8_LITTLE(c + 8,x2);
    U32TO8_LITTLE(c + 12,x3);
    U32TO8_LITTLE(c + 16,x4);
    U32TO8_LITTLE(c + 20,x5);
    U32TO8_LITTLE(c + 24,x6);
    U32TO8_LITTLE(c + 28,x7);
    U32TO8_LITTLE(c + 32,x8);
    U32TO8_LITTLE(c + 36,x9);
    U32TO8_LITTLE(c + 40,x10);
    U32TO8_LITTLE(c + 44,x11);
    U32TO8_LITTLE(c + 48,x12);
    U32TO8_LITTLE(c + 52,x13);
    U32TO8_LITTLE(c + 56,x14);
    U32TO8_LITTLE(c + 60,x15);

    if (bytes <= 64) {
      if (bytes < 64) {
#if (USE_MEMCPY == 1)
        memcpy(ctarget, c, bytes);
#else
        for (i = 0;i < bytes;++i) ctarget[i] = c[i];
#endif
      }
      x->input[12] = j12;
      x->input[13] = j13;
      return;
    }
    bytes -= 64;
    c += 64;
    m += 64;
  }
}

int main(void) {
  return 0;
}
