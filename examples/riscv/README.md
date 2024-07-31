# HolBA RISC-V examples

## Prerequisites

### Intalling the RISC-V cross-compilation toolchain

On Debian-based Linux distributions such as Ubuntu, it is possible to install RISC-V toolchain with `apt install gcc-riscv64-linux-gnu`.

To instead build and install from source, clone the RISC-V GNU Compiler Toolchain from GitHub:

```shell
git clone https://github.com/riscv/riscv-gnu-toolchain
```

Install the prerequisites, e.g., on Debian-based distributions such as Ubuntu:

```shell
sudo apt-get install autoconf automake autotools-dev curl python3 python3-pip libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev ninja-build git cmake libglib2.0-dev
```

Configure and build Linux cross-compiler:

```shell
./configure --prefix=/path/to/riscv
make linux
```

### Building HolBA

See the [general README](https://github.com/kth-step/HolBA/blob/master/README.md) for information on how to build HolBA.

## Binary verification workflow

### 0. RISC-V program

- RISC-V programs must be given in `.da` format for RV64
- C programs should ideally be compiled with `-O1` before disassembly (fewer instructions, close correspondence)

Example C function that increments an unsigned 64-bit integer:
```c
#include <stdint.h>

uint64_t incr(uint64_t i) {
  return i + 1;
}
```

Compile `incr.c` to produce the binary program `incr`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -o incr incr.c
```

Disassemble `incr`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-objdump -d incr > incr.da
```

Relevant contents of `incr.da`:
```assembly
incr:     file format elf64-littleriscv


Disassembly of section .text:

0000000000010488 <incr>:
   10488:	00150513          	addi	a0,a0,1
   1048c:	00008067          	ret
```

### 1. Lifting the RISC-V program to BIR

- requires manual specification of code area addresses, for all code included in the binary program
- the lifting stores HOL4 constants for the BIR program, the original binary program, and a lifting theorem for use in backlifting
- **automatic** once arguments (program memory boundaries) are given inside HOL4
- Notice: the code area addresses have to be accurate, i.e., the end boundary is the address of the last instruction plus 4 in case of RISC-V with 32-bit instructions

Example:

```sml
val _ = lift_da_and_store "incr" "incr.da" da_riscv
 ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10498));
```

### 2. RISC-V program boundaries and contract

- manually written in HOL4
- expressed using the [L3](https://acjf3.github.io/l3/index.html) model of RISC-V on pre- and post-states
- specifications must use variables to connect pre and post states

Example:

```sml
Definition incr_init_addr_def:
 incr_init_addr : word64 = 0x10488w
End

Definition incr_end_addr_def:
 incr_end_addr : word64 = 0x1048cw
End

Definition riscv_incr_pre_def:
 riscv_incr_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_incr_post_def:
 riscv_incr_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 + 1w)
End
```

### 3. High Level BIR contract

- BIR expressions with arbitrary HOL4 terms and free variables
- not suitable for symbolic execution
- manually written in HOL4

Example:

```sml
Definition bir_incr_pre_def:
 bir_incr_pre (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))
End

Definition bir_incr_post_def:
 bir_incr_post (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
   BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (pre_x10 + 1w)))
End
```

### 4. BSPEC contract

- BIR expressions that are closed except for occurrences of free variables
- may require conditions on memory accesses (alignment)
- used for symbolic execution
- manually written in HOL4

Example:

```sml
Definition bspec_incr_pre_def:
 bspec_incr_pre (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))
End

Definition bspec_incr_post_def:
 bspec_incr_post (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x10)) (BExp_Const (Imm64 1w)))
End
```

### 5. Connecting RISC-V and High Level BIR contracts

- RISC-V precondition implies BIR precondition
- BIR postcondition implies RISC-V postcondition
- manually written in HOL4

Example:

```sml
Theorem incr_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir (riscv_incr_pre pre_x10) (bir_incr_pre pre_x10)
Proof
(* ... *)
QED

Theorem incr_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_incr_post pre_x10) (\l. bir_incr_post pre_x10) ls
Proof
(* ... *)
QED
```

### 6. Connecting High Level BIR and BSPEC contracts

- BIR precondition implies BSPEC precondition
- BSPEC postcondition implies BIR postcondition
- manually written in HOL4

Example:

```sml
Theorem incr_bir_pre_imp_bspec_pre:
 bir_exp_is_taut 
  (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bir_incr_pre pre_x10))
   (bspec_incr_pre pre_x10))
Proof
(* ... *)
QED

Theorem incr_bspec_post_imp_bir_post:
 bir_exp_is_taut
  (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bspec_incr_post pre_x10))
   (bir_incr_post pre_x10))
Proof
(* ... *)
QED
```

### 5. BIR symbolic execution analysis

- built on a [general theory of symbolic execution](https://arxiv.org/abs/2304.08848) instantiated for BIR
- **automatic** inside HOL4 if parameters have the right shape

Example:

```sml
Theorem incr_symb_analysis_thm:
 symb_hl_step_in_L_sound (bir_symb_rec_sbir bir_incr_prog_tm) (* ... *)
Proof
(* generated *)
QED
```

### 6. Specifying and proving BSPEC contracts using symbolic analysis results

- requires manual specification of beginning and end program labels for contract
- **automatic** inside HOL4 if parameters have the right shape 

Example:

```sml
Theorem bspec_cont_incr:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 incr_init_addr))
  {BL_Address (Imm64 incr_end_addr)} {} (bspec_incr_pre pre_x10)
   (\l. if l = BL_Address (Imm64 incr_end_addr) then bspec_incr_post pre_x10
        else bir_exp_false)
Proof
(* application of symbolic analysis results *)
QED
```

### 6. Proving High Level BIR Contract

- built on a [general Hoare-style logic](https://doi.org/10.1007/978-3-030-58768-0_11) for unstructured programs
- requires auxiliary results from above steps
- **automatic** inside HOL4 if parameters have the right shape

Example:

```sml
Theorem bir_cont_incr:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 incr_init_addr))
  {BL_Address (Imm64 incr_end_addr)} {} (bir_incr_pre pre_x10)
  (\l. if l = BL_Address (Imm64 incr_end_addr) then bir_incr_post pre_x10
       else bir_exp_false)
Proof
(* application of Hoare logic automation *)
QED
```

### 7. Backlifting High Level BIR contract to RISC-V binary

- built on a [general Hoare-style logic](https://doi.org/10.1007/978-3-030-58768-0_11) for unstructured programs 
- requires collecting auxiliary results from above steps
- **automatic** inside HOL4 if all parameters have the right shape

Example:

```sml
Theorem riscv_incr_contract_thm:
 riscv_cont bir_foo_progbin incr_init_addr {incr_end_addr}
  (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)
Proof
(* application of backlifting automation *)
QED
```
