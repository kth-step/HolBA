# Vendored RISC-V L3 model and step library

The files in `model/` and `step/` are copies of HOL4's RISC-V L3 model and its step library
from a fork of HOL4 that moves the model to the privileged architecture 1.13 (M-mode, S-mode
and U-mode, PMP, Sv39, Sv48 and Sv57 address translation, RV64GC):

| | |
|---|---|
| Upstream | https://github.com/didriklundberg/HOL, branch `riscv-l3-smode`, the branch of HOL4's pull request 2204 (https://github.com/HOL-Theorem-Prover/HOL/pull/2204) |
| Commit | `8c9e650afb48ef409eef00db0800afe8b8e569d1` (2026-11-20) |
| Same files | the files of `model/` and of `step/` are byte-identical to their upstream counterparts at that commit, except for one line each of `step/riscv_stepScript.sml` and `step/riscv_stepLib.sml` (the local patch below) |
| Upstream directory | `examples/l3-machine-code/riscv/` |
| L3 version | L3-2018-02-09 (the model files are L3's HOL4 and SML exports of `src/riscv.spec`) |
| HOL4 used by HolBA | `trindemossen-2-v10` (upstream builds its files against HOL4 `develop`) |

The L3 source of the model, `src/riscv.spec`, is not vendored: it is in the upstream directory
at the commit above, with `src/README.md` and `src/Makefile` saying how to regenerate the
model from it. It and the step library cite the RISC-V specification, version 20260120, by
section and printed page. The hypotheses that the M-mode step theorems carry are listed in the
header of `step/riscv_step_selftest.sml`; why none of them is on `satp`, and what HolBA lifts
of it, is in the comments of `src/theory/tools/lifter/bir_lifting_machinesScript.sml`.

## Files

| HolBA | Upstream (`examples/l3-machine-code/riscv/`) | Changed here |
|---|---|---|
| `model/riscvScript.sml` | `model/riscvScript.sml` | no |
| `model/riscvLib.sml`, `model/riscvLib.sig` | `model/riscvLib.sml`, `model/riscvLib.sig` | no |
| `model/riscv.sml`, `model/riscv.sig` | `model/riscv.sml`, `model/riscv.sig` | no |
| `step/riscv_stepScript.sml` | `step/riscv_stepScript.sml` | the local patch |
| `step/riscv_stepLib.sml` | `step/riscv_stepLib.sml` | the local patch |
| `step/riscv_stepLib.sig` | `step/riscv_stepLib.sig` | no |
| `step/riscv_nextScript.sml` | `step/riscv_nextScript.sml` | no |
| `step/riscv_refineScript.sml` | `step/riscv_refineScript.sml` | no |
| `step/riscv_step_selftest.sml` | `step/selftest.sml` | renamed |
| `model/Holmakefile`, `step/Holmakefile` | | HolBA's own |

`riscv_nextTheory` cuts the step function `Next` of the model into its parts, and
`riscv_refineTheory` proves that `Next` and the step library's `NextRISCV` step to states that
agree up to the fields that only the model's logging and counting use, for an instruction that
reads no counter CSR (`Next_NextRISCV_ghost`). HolBA's lifter uses neither; they are built with
the rest of `step/`.

Upstream's `prog/`, `decompiler/` and `src/` are not vendored. The Holmakefiles are HolBA's:
they build no heaps and find L3's `common` and `lib` directories under `$(HOLDIR)`.

## Compatibility with HOL4 `trindemossen-2-v10`

Upstream's files at the commit above are written for HOL4 `develop`. They use one interface
that `trindemossen-2-v10` does not have, and the copy carries one local patch for it:
`step/riscv_stepScript.sml` and `step/riscv_stepLib.sml` show assumptions with
`show_assums := true` instead of `HOLFlags.set_bflag (Parse.show_assums, true)`;
`trindemossen-2-v10` has no `HOLFlags`.

## The selftest

The selftest is renamed so that HolBA's `make tests`, which runs every `selftest.sml`, does
not pick it up: it takes some minutes. Run it with `Holmake selftest` in `step/`, which
compiles it as upstream does and writes `step/riscv_step_selftest.log`. It runs the step
library on one encoding of every entry of `riscv_dict`, on a read and two writes of every CSR
and on edge cases, and checks that each step theorem has exactly the hypotheses that the M-mode
contract in its header allows. Under `trindemossen-2-v10` its 1,521 checks pass, in about four
minutes.

## Resynchronising

1. Copy the files in the table from the new upstream commit, for example with
   `git -C <HOL fork> show <commit>:examples/l3-machine-code/riscv/<file> > <HolBA file>`.
2. Apply the local patch above again while HolBA's HOL4 has no `HOLFlags` (and patch any new
   use of an interface that HolBA's HOL4 lacks), and update this file: commit, date, the local
   patches. `diff` of each patched file against its upstream counterpart must show the patches
   and nothing else.
3. Build `model/` and `step/` with HolBA's HOL4 (`Holmake` in each), and run
   `Holmake selftest` in `step/`.
4. Rebuild the lifter (`src/theory/tools/lifter`, `src/tools/lifter`, the backlifter) and run
   `src/tools/lifter/selftest_riscv.sml`. A change of the step theorems shows up as a change of
   `selftest_riscv.log`; regenerate the log and check every changed block before committing it.
