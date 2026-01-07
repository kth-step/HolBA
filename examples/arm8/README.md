# HolBA ARMv8 examples

## Prerequisites

### Installing ARMv8 cross-compilation toolchain

On Debian-based Linux distributions such as Ubuntu, it is possible to install ARMv8 compiler via `apt`:
```shell
apt install gcc-aarch64-linux-gnu
```

### Building HolBA

See the [general README](https://github.com/kth-step/HolBA/blob/master/README.md) for information on how to build HolBA.

## Binary verification workflow

### 0. ARMv8 program

- ARMv8 programs must be given in `.da` format for AArch64 instruction set
- C programs should ideally be compiled with `-O1` before disassembly (fewer instructions, close correspondence)
- to enable linking, include a (dummy) `main` function

Example C program that increments an unsigned 64-bit integer:
```c
#include <stdint.h>

uint64_t incr(uint64_t i) {
  return i + 1;
}

int main(void) {
  uint64_t i = incr(0);
  return i;
}
```

Compile and link `incr.c` to produce the binary program `incr`:
```shell
aarch64-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -O1 -o incr incr.c
```

Disassemble `incr`:
```shell
aarch64-linux-gnu-objdump -d incr > incr.da
```

Relevant contents of `incr.da`:
```assembly
incr:     file format elf64-littleaarch64

Disassembly of section .text:

0000000000000718 <incr>:
 718:   91000400        add     x0, x0, #0x1
 71c:   d65f03c0        ret
```

### 1. Lifting the ARMv8 program to BIR

- requires manual specification of code area addresses, for all code included in the binary program
- the lifting stores HOL4 constants for the BIR program, the original binary program, and a lifting theorem for use in backlifting
- **automatic** once arguments (names and code area boundaries) are given inside HOL4
- the code area addresses have to be accurate, i.e., the end boundary is the address of the last instruction plus 4 in case of 32-bit instructions as in AArch64

Example:

```sml
val _ = lift_da_and_store "incr" "incr.da" da_arm8
 ((Arbnum.fromInt 0x718), (Arbnum.fromInt 0x728));
```

### 2. ARMv8 program boundaries and contract

- manually written in HOL4
- expressed using the [L3](https://acjf3.github.io/l3/index.html) model of ARMv8 on pre- and post-states
- specifications must use variables to connect pre and post states

Example:

```sml
Definition incr_init_addr_def:
 incr_init_addr : word64 = 0x718w
End

Definition incr_end_addr_def:
 incr_end_addr : word64 = 0x71cw
End

Definition arm8_incr_pre_def:
 arm8_incr_pre (pre_x0:word64) (m:arm8_state) : bool =
  (m.REG 0w = pre_x0)
End

Definition arm8_incr_post_def:
 arm8_incr_post (pre_x0:word64) (m:arm8_state) : bool =
  (m.REG 0w = pre_x0 + 1w)
End
```
### 3. BIR contract

- uses BIR boolean expressions that are closed except for occurrences of free HOL4 variables
- may require conditions on memory accesses (alignment)
- used for symbolic execution
- manually written in HOL4
- the subset of BIR used is referred to as BSPEC

Example:

```sml
Definition bspec_incr_pre_def:
 bspec_incr_pre (pre_x0:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))
End

Definition bspec_incr_post_def:
 bspec_incr_post (pre_x0:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x0)) (BExp_Const (Imm64 1w)))
End
```

### 4. Connecting ARMv8 and BIR contracts

- ARMv8 precondition implies BIR precondition
- BIR postcondition implies ARMv8 postcondition
- manually written in HOL4

Example:

```sml
Theorem incr_arm8_pre_imp_bspec_pre_thm:
 bir_pre_arm8_to_bir (arm8_incr_pre pre_x0) (bspec_incr_pre pre_x0)
Proof
(* ... *)
QED

Theorem incr_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8 (arm8_incr_post pre_x0) (\l. bspec_incr_post pre_x0) ls
Proof
(* ... *)
QED
```

### 5. BIR symbolic execution analysis

- built on a [general theory of symbolic execution](https://arxiv.org/abs/2304.08848), instantiated for BIR
- **automatic** inside HOL4 if parameters have the right shape
- a summarizing collection of performance evaluations for the benchmark programs can be found in [experiment_data.log](experiment_data.log)
- at the end of an execution, a set of profiling measurements are printed into the respective HOL4 build log, e.g., `aes/.hollogs/aes_symb_execTheory`

Example:

```sml
Theorem incr_symb_analysis_thm:
 symb_hl_step_in_L_sound (bir_symb_rec_sbir bir_incr_prog_tm) (* ... *)
Proof
(* generated *)
QED
```

### 6. Specifying and proving BIR contract using symbolic analysis results

- requires manual specification of beginning and end program labels for contract
- **automatic** inside HOL4 if parameters have the right shape 

Example:

```sml
Theorem bspec_cont_incr:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 incr_init_addr))
  {BL_Address (Imm64 incr_end_addr)} {} (bspec_incr_pre pre_x0)
   (\l. if l = BL_Address (Imm64 incr_end_addr) then bspec_incr_post pre_x0
        else bir_exp_false)
Proof
(* application of symbolic analysis results *)
QED
```

### 7. Backlifting BIR contract to ARMv8 binary

- built on a [general Hoare-style logic](https://doi.org/10.1007/978-3-030-58768-0_11) for unstructured programs, instantiated for ARMv8
- requires collecting auxiliary results from above steps
- **automatic** inside HOL4 if all parameters have the right shape

Example:

```sml
Theorem arm8_incr_contract_thm:
 arm8_cont bir_incr_progbin incr_init_addr {incr_end_addr}
  (arm8_incr_pre pre_x0) (arm8_incr_post pre_x0)
Proof
(* application of backlifting automation *)
QED
```
