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

## The RISC-V model

### Provenance

HolBA lifts RISC-V machine code with HOL4's [L3](https://acjf3.github.io/l3/index.html) model of
RISC-V and its step library, in the version of the `riscv-l3` branch of a fork of HOL4
(https://github.com/didriklundberg/HOL), which moves the model to the RISC-V privileged
architecture 1.13: RV64GC with M-mode, U-mode and physical memory protection (PMP), and no S-mode
or virtual memory. HolBA keeps a copy of the generated model and of the step library in
[`src/shared/l3-machine-code/riscv`](../../src/shared/l3-machine-code/riscv); its `VENDORING.md`
gives the upstream commit, the changes made for HOL4 `trindemossen-2` and how to update the copy.
The L3 source of the model (`src/riscv.spec`) and the design of its privileged architecture
(`doc/design-privileged.md`, which defines the hypotheses H1 to H6 below) are in the upstream
directory `examples/l3-machine-code/riscv`.

This model replaces an earlier, hand-edited one of the privileged architecture 1.7, in which
`mstatus` held the current privilege. For lifted programs this means that the BIR variable `MPRV`
is now `priv`, that `mstatus` has the layout of version 1.13, and that every lifted block asserts
the M-mode contract below.

### What lifts

The lifter lifts code that runs in M-mode, one instruction at a time:

- RV64I and the M extension;
- the A extension, except `sc.w` and `sc.d` (the load reservation is not lifted);
- the C extension (compressed instructions);
- `fence`, `fence.i`, and the Zicsr instructions on the CSRs that are lifted (listed below);
- writes of the CSRs that the model stores but the lifter does not lift (`medeleg`, `mideleg`,
  `menvcfg` and the S-mode CSRs), as blocks without an assignment: these CSRs have no effect on
  M-mode code;
- `ecall`, `ebreak` and `c.ebreak`, a trap to M-mode: the block sets `priv` (to 3), `mstatus`,
  `mepc`, `mcause` and `mtval`, and ends in a jump to the base address in `mtvec`;
- `mret`: the block sets `priv` to the privilege in `mstatus.MPP` and updates `mstatus`, and it
  ends in a jump to `mepc`;
- `wfi` and `sfence.vma`, which do nothing in M-mode;
- the loads, stores and moves of the D extension (`fld`, `fsd`, `c.fld`, `c.fsd`, `c.fldsp`,
  `c.fsdsp`, `fmv.x.d`, `fmv.d.x`), and `fsw` and `fmv.x.w` of the F extension.

The BIR variables of a lifted program are `x0` to `x31`, `f0` to `f31`, `MEM8`, `priv` (the
privilege, 8 bits: 3 for M-mode, 0 for U-mode), the CSRs `mstatus`, `mtvec`, `mie`, `mip`,
`mscratch`, `mepc`, `mcause`, `mtval`, `mhartid`, `mcounteren`, `mcountinhibit`, `scounteren`,
`pmpcfg0`, `pmpcfg2` and `pmpaddr0` to `pmpaddr15` (64 bits each; `mstatus`, `mie`, `mip` and
`mcause` with the bit layout of the privileged specification), and `procID` (the hart number),
`extMEIP` and `extSEIP` (the external interrupt lines), which no instruction changes and which a
read of `mip` depends on.

These do not lift: `sc.w` and `sc.d`; reads of the counters (`mcycle`, `minstret`, `cycle` and so
on), of `misa`, of the floating-point CSRs and of the other CSRs that are not lifted; writes of
`misa`; `flw` and `fmv.w.x`, which write a NaN-boxed value (the 32-bit value with 32 one-bits
above it, a concatenation that the lifter does not translate); floating-point arithmetic and
conversions; `sret` and illegal instructions; and code that runs in U-mode.

`src/tools/lifter/selftest_riscv.sml` lifts a sample of each class (its log is
`selftest_riscv.log`). The RISC-V section of `src/tools/lifter/README` has the details.

### What a lifted block asserts

The step theorems of the model describe a step in M-mode under a contract on the machine state,
and the lifter turns each hypothesis of a step theorem into an assertion at the start of the BIR
block of the instruction. Symbolic execution has to show these assertions:

| Hypothesis | BIR assertion | In the blocks of |
|---|---|---|
| H1: the hart is in M-mode | `priv = 3` | every instruction |
| H3: no PMP entry is locked | `pmpcfg0 & 0x8080808080808080 = 0`, and the same for `pmpcfg2` | every instruction |
| H6: interrupts are disabled | bit 3 of `mstatus` (`MIE`) is clear | every instruction |
| H2: data accesses use the privilege M | bit 17 of `mstatus` (`MPRV`) is clear | loads, stores, AMOs, `lr` |
| H5: the address is aligned | `BExp_Aligned` of the address | loads, stores, AMOs and `lr` of 2, 4 and 8 bytes |
| H4: every PMP entry is OFF or NAPOT | `((pmpcfg0 >> 1) ^ pmpcfg0) & 0x0808080808080808 = 0`, and the same for `pmpcfg2` | loads, stores, AMOs and `lr` of 8 bytes |
| floating point is on | `mstatus & 0x6000 <> 0` (`FS` is not Off) | the F and D instructions |

The assertion of the alignment (H5) is not new, and a store also asserts, as before, that it does
not write the lifted code (`BExp_unchanged_mem_interval_distinct`). The other assertions are new:
4 in every block, 5 in the block of a data access of at most 4 bytes and 7 in that of an 8-byte
access, and one more for floating point.

They are assertions, and not part of `riscv_state_is_OK` (the predicate of the machine record in
`src/theory/tools/lifter/bir_lifting_machinesScript.sml`, which must hold before and after every
lifted instruction), because lifted instructions change them: `mret` the privilege and
`mstatus`, the CSR instructions `mstatus` and the PMP configuration, and `ecall` and `ebreak`
`mstatus`. `riscv_state_is_OK` holds only what no lifted instruction changes: there is no
exception and no pending control transfer, the hart is RV64 (`misa.MXL`, which is read-only) and
the C extension is enabled (`misa.C`, which only a write of `misa` can change, and no write of
`misa` lifts). With `misa.C`, compressed instructions and jumps to targets that are not 4-byte
aligned need no assertion.

A contract therefore assumes the M-mode contract: its RISC-V precondition states `riscv_mmode m`
and its BIR precondition `bir_riscv_mmode_pre` (both in `bir_riscv_backlifterTheory`), as the
steps below show.

### Changes from the previous model

Every instruction that lifted with the previous model still lifts, to the same block apart from
the new assertions, except for these changes (`src/tools/lifter/selftest_riscv.log` shows the
blocks):

- `jalr`, and with it `ret`, `c.jr` and `c.jalr`, no longer asserts that bit 0 of its target is
  clear: the instruction clears it, and with `misa.C` a target needs no more alignment than that;
- the lifting theorem of `jal` and `c.j` no longer has the hypothesis that bit 0 of the pc is
  clear, which the lifter now discharges;
- `csrwi` with a zero immediate writes the CSR, which the previous model, against the
  specification, did not: `csrwi mstatus, 0` assigns 0 to `mstatus`, and `csrwi mie, 0` to `mie`,
  which is now lifted;
- the mask `~x` of `csrrc` is `BExp_UnaryExp BIExp_Not x` instead of `-1 * x - 1`;
- `csrr mip` no longer reads a stored register only: as in the specification, MSIP and MTIP come
  from the CLINT in the memory and MEIP and SEIP from the external interrupt lines;
- the BIR variable `MPRV`, which held the privilege, is `priv`.

New are the lifting of `ecall`, `ebreak` and `c.ebreak`, of `amomin`, `amomax`, `amominu` and
`amomaxu`, of `mret`, `wfi` and `sfence.vma`, of the floating-point loads, stores and moves, and of
the CSR instructions on the CSRs that the previous model did not have.

## Binary verification workflow

### 0. RISC-V program

- RISC-V programs must be given in `.da` format for the RV64GC instruction set (see [What lifts](#what-lifts) for the instructions that the lifter supports)
- we found that C programs compiled with `-O1` before disassembly are easier to specify and verify (fewer instructions, close correspondence to source code)
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
- **automatic** once arguments (names and code area boundaries) are given inside HOL4
- the code area addresses have to be accurate, i.e., the end boundary is the address of the last instruction plus its size: 4 for 32-bit instructions as in RV64G, 2 for 16-bit (compressed) instructions

Example:

```sml
val _ = lift_da_and_store "incr" "incr.da" da_riscv
 ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10498));
```

### 2. RISC-V program boundaries and contract

- manually written in HOL4
- expressed using the [L3](https://acjf3.github.io/l3/index.html) model of RISC-V on pre- and post-states
- specifications must use variables to connect pre and post states
- the lifted code runs in M-mode, and every lifted block asserts the M-mode contract of the
  model's step theorems (see the RISC-V section of `src/tools/lifter/README`), so a precondition
  includes `riscv_mmode m` (`bir_riscv_backlifterTheory`): the privilege is M, `mstatus.MIE` and
  `mstatus.MPRV` are clear, and no PMP entry is locked or anything but OFF or NAPOT
- the postconditions of the examples do not state `riscv_mmode m` again, so a contract does not
  say that the M-mode contract still holds where it ends; a contract that is to be followed by
  another one (composition, `src/tools/comp`) has to state it in its postconditions too, which
  symbolic execution shows for code that writes none of `priv`, `mstatus`, `pmpcfg0` and
  `pmpcfg2` (the BIR variables of the contract keep their initial values):
  `bir_post_bir_to_riscv_mmode_conj` (`bir_riscv_backlifterTheory`) adds `riscv_mmode m` to the
  RISC-V postcondition and `bir_riscv_mmode_post` to the BIR postcondition of the implication
  between them (`bir_riscv_mmode_post` is the M-mode contract written without `BExp_word_bit`,
  which the transfer of a BIR contract does not accept in a postcondition)

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
  (riscv_mmode m /\
   m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_incr_post_def:
 riscv_incr_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 + 1w)
End
```
### 3. BIR contract

- uses BIR boolean expressions that are closed except for occurrences of free HOL4 variables
- may require conditions on memory accesses (alignment)
- the precondition starts with `bir_riscv_mmode_pre`, the M-mode contract as a BIR expression on
  the variables `priv`, `mstatus`, `pmpcfg0` and `pmpcfg2`, so that symbolic execution can show
  that the assertions of the lifted blocks hold
- used for symbolic execution
- manually written in HOL4
- the subset of BIR used is referred to as BSPEC

Example:

```sml
Definition bspec_incr_pre_def:
 bspec_incr_pre (pre_x10:word64) : bir_exp_t =
  BExp_BinExp BIExp_And
   ^(rhs (concl bir_riscv_mmode_pre_def))
   (BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x10" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x10)))
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

### 4. Connecting RISC-V and BIR contracts

- RISC-V precondition implies BIR precondition
- BIR postcondition implies RISC-V postcondition
- manually written in HOL4
- `bir_pre_riscv_to_bir_mmode_conj` (`bir_riscv_backlifterTheory`) takes care of the M-mode
  conjuncts: applied with `MATCH_MP_TAC`, it leaves the implication of the rest of the
  preconditions

Example:

```sml
Theorem incr_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir (riscv_incr_pre pre_x10) (bspec_incr_pre pre_x10)
Proof
(* ... *)
QED

Theorem incr_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_incr_post pre_x10) (\l. bspec_incr_post pre_x10) ls
Proof
(* ... *)
QED
```

### 5. BIR symbolic execution analysis

- built on a [general theory of symbolic execution](https://arxiv.org/abs/2304.08848v2), instantiated for BIR
- **automatic** inside HOL4 if parameters have the right shape
- a summarizing collection of performance evaluations for the benchmark programs can be found in [experiment_data.log](experiment_data.log);
  these were measured with an earlier version of HolBA and of the RISC-V model, before the lifted blocks asserted the M-mode contract,
  whose assertions symbolic execution now also has to show, which makes it slower
- at the end of an execution, a set of profiling measurements are printed into the respective HOL4 build log, e.g., `aes/.hol/logs/aes_symb_execTheory`

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
  {BL_Address (Imm64 incr_end_addr)} {} (bspec_incr_pre pre_x10)
   (\l. if l = BL_Address (Imm64 incr_end_addr) then bspec_incr_post pre_x10
        else bir_exp_false)
Proof
(* application of symbolic analysis results *)
QED
```

### 7. Backlifting BIR contract to RISC-V binary

- built on a [general Hoare-style logic](https://doi.org/10.1016/j.jlamp.2025.101099) for unstructured programs, instantiated for RISC-V
- requires collecting auxiliary results from above steps
- **automatic** inside HOL4 if all parameters have the right shape

Example:

```sml
Theorem riscv_incr_contract_thm:
 riscv_cont bir_incr_progbin incr_init_addr {incr_end_addr}
  (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)
Proof
(* application of backlifting automation *)
QED
```
