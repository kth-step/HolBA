# Input program
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
```
   0:	d10043ff 	sub	sp, sp, #0x10
   4:	f90007e0 	str	x0, [sp, #8]
   8:	f90003e1 	str	x1, [sp]
   c:	f94007e2 	ldr	x2, [sp, #8]
  10:	f94003e3 	ldr	x3, [sp]
  14:	f94007e4 	ldr	x4, [sp, #8]
  18:	f94003e5 	ldr	x5, [sp]
  1c:	14000007 	b	38 <add_reg+0x38>
  20:	aa0303e0 	mov	x0, x3
  24:	91000400 	add	x0, x0, #0x1
  28:	aa0003e3 	mov	x3, x0
  2c:	aa0203e0 	mov	x0, x2
  30:	d1000400 	sub	x0, x0, #0x1
  34:	aa0003e2 	mov	x2, x0
  38:	aa0203e0 	mov	x0, x2
  3c:	f100001f 	cmp	x0, #0x0
  40:	54ffff0c 	b.gt	20 <add_reg+0x20>
  44:	aa0303e0 	mov	x0, x3
  48:	910043ff 	add	sp, sp, #0x10
  4c:	d65f03c0 	ret
```
The produced binary consists of four blocks
1. from `0x0` to `0x1c`: allocates 16 bytes on the stack; pushes the
   parameters on the stack; pushes the two parameters on the stack;
   copies the first parameter (`x0`) to `x2`
   and `x4`; copies the second parameter (`x1`) to `x3`
   and `x4`; jumps to the second block
2. from `0x38` to `0x40`: computes the while condition and exit the
   loops of the condition is not satisfied. Notice that the loop
   condition is computed by updating the CPU flags (using `cmp`) and
   that if the condition holds (i.e. `x2 > 0`) then `b.gt 20`
   jumps back to the loop body
3. from `0x20` to `0x34`: increases `y` (i.e. `x3`) and decreases `x`
   (i.e. `x2`) and jumps to the second block to check the while
   condition
4. from `0x44` to `0x4c`: copies the result in the register `x0`; frees
   the stack frame; and returns from the function.

# Some notes on the examples
The `add_reg` function has some properties that make our analysis
simpler:
* there are no indirect jumps. We cannot currently automatically
  analyse code with indirect jumps, since the weakest precondition
  algorithm requires a static control flow graph.
* there are no multiplications among variables: non-linear arithmetic
  is an hard problem for SMT solvers, therefore analysing the
  algorithm would require to verify some support theorems that can be
  used as axioms in Z3
* memory is not updated. This dramatically reduce the problem size in
  Z3. A more detailed discussion regarding problems to handle memory
  accesses is in section 5 and 6.
  
