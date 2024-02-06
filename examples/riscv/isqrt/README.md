# RISC-V isqrt example

## isqrt program

We consider the following program which computes the
integer square root of a given unsigned 64-bit integer.

```c
#include <stdint.h>

uint64_t isqrt(uint64_t x) {
  uint64_t y = 0;
  while ((y+1)*(y+1) <= x) {
    y += 1;
  }
  return y;
}
```

## Compile and disassemble the isqrt program

Compile `isqrt.c` as a library, producing `isqrt.o`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -c -o isqrt.o isqrt.c
```

Compile `isqrt.c` to assembly, producing `isqrt.s` (optional):
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -S -o isqrt.s isqrt.c
```

Disassemble `isqrt.o`, producing `isqrt.da`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-objdump -d isqrt.o
```

## Lifting the isqrt program to BIR

The following command inside SML/HOL4 lifts the disassembled code to BIR:

```sml
val _ = lift_da_and_store "isqrt" "isqrt.da" ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
```

## BIR isqrt program and its properties

After lifting, the BIR program resides in the HOL4 term `bir_isqrt_prog`.
The program's BIR statements can be obtained by:
```sml
val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_swap_prog``;
```
