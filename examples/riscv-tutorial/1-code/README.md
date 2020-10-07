# 1 Input Program
We use a simple C program to demonstrate HolBA: a naive function that
adds two 64-bit integers. The function is defined in [src/add_reg.c](src/add_reg.c)

```C
int64_t add_reg (int64_t x, int64_t y) {
  register int64_t lx asm ("x2") = x;
  register int64_t ly asm ("x3") = y;
  register int64_t oldx asm ("x4") = x;
  register int64_t oldy asm ("x5") = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}
```
The program cam be
compiled by running `make`, which produces
[src/add_reg.da](src/add_reg.da).

TODO: Rest