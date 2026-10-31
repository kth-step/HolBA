# Vendored RISC-V L3 model and step library

The files in `model/` and `step/` are copies of HOL4's RISC-V L3 model and its step library
from a fork of HOL4 that moves the model to the privileged architecture 1.13 (M-mode and
U-mode, PMP, RV64GC):

| | |
|---|---|
| Upstream | https://github.com/didriklundberg/HOL, branch `riscv-l3` |
| Commit | `8f8ab4f206e9e6560c927e35754c447083520e06` (2026-10-31) |
| Upstream directory | `examples/l3-machine-code/riscv/` |
| L3 version | L3-2018-02-09 (the model files are L3's HOL4 and SML exports of `src/riscv.spec`) |
| HOL4 used by HolBA | `trindemossen-2` (upstream builds against HOL4 `develop`) |

The L3 source of the model, `src/riscv.spec`, is not vendored: it is in the upstream directory
at the commit above, with `src/README.md` and `src/Makefile` saying how to regenerate the
model from it. The design of the privileged architecture, including the hypotheses that the
M-mode step theorems carry (H1 to H6, `doc/design-privileged.md` §1.5), is in `doc/` there.

## Files

| HolBA | Upstream (`examples/l3-machine-code/riscv/`) | Changed here |
|---|---|---|
| `model/riscvScript.sml` | `model/riscvScript.sml` | no |
| `model/riscvLib.sml`, `model/riscvLib.sig` | `model/riscvLib.sml`, `model/riscvLib.sig` | no |
| `model/riscv.sml`, `model/riscv.sig` | `model/riscv.sml`, `model/riscv.sig` | no |
| `step/riscv_stepScript.sml` | `step/riscv_stepScript.sml` | patch 1 |
| `step/riscv_stepLib.sml` | `step/riscv_stepLib.sml` | patches 2 and 3 |
| `step/riscv_stepLib.sig` | `step/riscv_stepLib.sig` | no |
| `step/riscv_step_selftest.sml` | `step/selftest.sml` | renamed, patch 4 |
| `model/Holmakefile`, `step/Holmakefile` | | HolBA's own |

Upstream's `prog/`, `decompiler/`, `sim/`, `src/` and `doc/` are not vendored. The Holmakefiles
are HolBA's: they build no heaps and find L3's `common` and `lib` directories under `$(HOLDIR)`.

## Local patches

Each patch makes the vendored code build and run with HOL4 `trindemossen-2`, whose interfaces
differ from those of HOL4 `develop` in the three places below. Each is written so that it also
works with `develop`, so it can be applied upstream as it is.

1. `step/riscv_stepScript.sml`: the `fupdselfid` theorems (`r with f := r.f = r` for every
   field `f`) of `riscv_state`, `MachineCSR`, `mstatus`, `UserCSR` and `FPCSR` are proved in
   the script. The record package of `develop` generates them and puts them in the simpset of
   each record type; that of `trindemossen-2` does neither. The proof of `accrueFlags_update`
   names them, and `mret_eval` needs `mstatus_fupdselfid`, which is added to its last `simp`.
2. `step/riscv_stepLib.sml`, `run`: the failure of the step-theorem lookup (`find_rw`, which
   fails only when no theorem matches) is handled where the lookup is made, instead of by
   inspecting the `HOL_ERR` that it raises. `HOL_ERR` carries a record in `trindemossen-2` and
   an abstract `hol_error` (`message_of`, `top_function_of`) in `develop`.
3. `step/riscv_stepLib.sml`, `csr_rule`: the compset that reduces `CSRMap` and `write'CSRMap`
   to the branch of one CSR is built with `computeLib.new_compset` and `computeLib.compset_conv`
   from the rewrites of `computeLib.bool_compset` (listed in the code), instead of with
   `computeLib.copy`, `add_thms` and `add_conv` on `bool_compset`. In `develop` compsets are
   values that these functions return; in `trindemossen-2` `bool_compset` is a function and
   `add_thms` and `add_conv` update a compset in place.
4. `step/riscv_step_selftest.sml`, `must_step_with`: the message of the exception is read with
   `Feedback.exn_to_string` instead of `Feedback.message_of`, which `trindemossen-2` does not
   have.

The selftest is renamed so that HolBA's `make tests`, which runs every `selftest.sml`, does
not pick it up: it takes about six minutes. Run it with `Holmake selftest` in `step/`; it
writes `step/riscv_step_selftest.log`. With the patches it passes under `trindemossen-2`, and
it reports the same hypotheses for every class of instruction as unpatched upstream does
under `develop`. The step theorems of a sample of 47 instructions (loads, stores, jumps,
compressed instructions, AMOs, `LR`/`SC`, the CSR instructions on the CSRs that HolBA lifts,
`ECALL`, `EBREAK`, `MRET` and `WFI`) are identical in the two settings. The patched files
also build, and pass the selftest, under `develop`.

## Resynchronising

1. Copy the files in the table from the new upstream commit, for example with
   `git -C <HOL fork> show <commit>:examples/l3-machine-code/riscv/<file> > <HolBA file>`.
2. Reapply the patches that upstream has not taken (compare with the list above), and update
   this file: commit, date, patch list.
3. Build `model/` and `step/` with HolBA's HOL4 (`Holmake` in each), and run
   `Holmake selftest` in `step/`.
4. Rebuild the lifter (`src/theory/tools/lifter`, `src/tools/lifter`, the backlifter) and run
   `src/tools/lifter/selftest_riscv.sml`. A change of the step theorems shows up as a change of
   `selftest_riscv.log`; regenerate the log and check every changed block before committing it.
