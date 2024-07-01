# HolBA RISC-V examples

## Prerequisites

### Intalling the RISC-V cross-compilation toolchain

Clone the RISC-V GNU Compiler Toolchain:

```shell
git clone https://github.com/riscv/riscv-gnu-toolchain
```

Install the prerequisites, e.g., on Ubuntu:

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
- (on Debian-based distributions, it is possible to install RISC-V toolchain with `apt install gcc-riscv64-linux-gnu`, then simply use `riscv64-linux-gnu-gcc/objdump`)

Compile `foo.c` as a library, producing `foo.o`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -o foo.o foo.c
```

Disassemble `foo.o`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-objdump -d foo.o > foo.da
```

Contents of `foo.da`:
```
foo.o:     file format elf64-littleriscv


Disassembly of section .text:

0000000000000000 <foo>:
   0:	00150513          	addi	a0,a0,1
   4:	00008067          	ret
```

### 1. RISC-V contract

- manually written in HOL4
- expressed using the [L3](https://acjf3.github.io/l3/index.html) model of RISC-V on pre and post states
- specifications must use variables to connect pre and post states

Example:

```sml
Definition riscv_foo_pre_def:
 riscv_foo_pre x y z (m : riscv_state) = ...
End

Definition riscv_foo_post_def:
 riscv_foo_post x y z (m : riscv_state) = ...
End
```

### 2. Lifting RISC-V program to BIR

- requires manual specification of data area addresses, affecting symbolic execution
- the lifting stores HOL4 constants for the BIR program, original binary program, and a lifting theorem for use in backlifting
- **automatic** once arguments are given inside HOL4

Example:

```sml
val _ = lift_da_and_store "foo" "foo.da" da_riscv
  ((Arbnum.fromInt 0), (Arbnum.fromInt 0x30));
```

### 3. High Level BIR contract

- manually written in HOL4 as BIR expressions with arbitrary HOL4 terms and free variables
- not suitable for symbolic execution

Example:

```sml
Definition bir_foo_pre_def:
  bir_foo_pre x y z : bir_exp_t = ...
End

Definition bir_foo_post_def:
 bir_incr_post x y z : bir_exp_t = ...
End
```

### 4. BSPEC contract

- currently manually written in HOL4 as BIR expressions that are closed except for occurrences of free variables
- requires conditions on memory accesses (alignment)
- used for symbolic execution

Example:

```sml
Definition bspec_foo_pre_def:
 bspec_foo_pre x y z : bir_exp_t = ...
End

Definition bspec_foo_post_def:
 bspec_incr_post x y z : bir_exp_t = ...
End
```

### 5. Connecting RISC-V and High Level BIR contracts

- RISC-V precondition implies BIR precondition
- BIR postcondition implies RISC-V postcondition
- manually written proofs in HOL4

Example:

```sml
Theorem foo_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir (riscv_foo_pre x y z) (riscv_foo_pre x y z)
Proof
(* ... *)
QED

Theorem foo_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_foo_post x y z) (\l. bir_foo_post x y z) ls
Proof
(* ... *)
QED
```

### 6. Connecting High Level BIR and BSPEC contracts

- BIR precondition implies BSPEC precondition
- BSPEC postcondition implies BIR postcondition
- manually written proofs in HOL4

```sml
Theorem foo_bir_pre_imp_bspec_pre:
 bir_exp_is_taut (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bir_foo_pre pre_x10))
   (bspec_foo_pre pre_x10))
Proof
(* ... *)
QED
```

```sml
Theorem foo_bspec_post_imp_bir_post:
 bir_exp_is_taut (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bspec_foo_post pre_x10))
    (bir_foo_post pre_x10))
Proof
(* ... *)
QED
```

### 5. BIR symbolic execution analysis

- built on a [general theory of symbolic execution](https://arxiv.org/abs/2304.08848) instantiated for BIR
- requires knowing BIR program address bounds
- **automatic** inside HOL4 if parameters have the right shape

Example:

```sml
Theorem foo_symb_analysis_thm:
 symb_hl_step_in_L_sound (bir_symb_rec_sbir bir_foo_prog_tm) (* ... *)
Proof
(* generated *)
QED
```

### 6. Specifying and proving BSPEC contracts using symbolic analysis results

- requires manual specification of beginning and end program labels for contract
- **automatic** inside HOL4 if parameters have the right shape 

Example:

```sml
Theorem bspec_cont_foo:
 bir_cont bir_foo_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 30w)} {} (bspec_foo_pre x y z)
   (\l. if l = BL_Address (Imm64 30w) then (bspec_incr_post x y z)
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
val bir_cont_foo_thm = use_post_weak_rule_simp
 (use_pre_str_rule_simp bspec_cont_foo foo_bir_pre_imp_bspec_pre)
 ``BL_Address (Imm64 4w)`` foo_bspec_post_imp_bir_post;

Theorem bir_cont_foo:
 bir_cont bir_foo_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_foo_pre pre_x10)
  (\l. if l = BL_Address (Imm64 4w) then (bir_foo_post pre_x10)
       else bir_exp_false)
Proof
 ACCEPT_TAC bir_cont_foo_thm
QED
```

### 7. Backlifting High Level BIR contract to RISC-V binary

- built on a [general Hoare-style logic](https://doi.org/10.1007/978-3-030-58768-0_11) for unstructured programs 
- requires collecting auxiliary results from above steps
- **automatic** inside HOL4 if all parameters have the right shape

Example:

```sml
Theorem riscv_incr_contract_thm:
 riscv_cont bir_foo_progbin 0w {30w} (riscv_foo_pre x y z) (riscv_foo_post x y z)
Proof
(* application of backlifting automation *)
QED
```
