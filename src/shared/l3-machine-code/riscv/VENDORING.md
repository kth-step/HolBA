# Vendored RISC-V L3 model and step library

The files in `model/` and `step/` are copies of HOL4's RISC-V L3 model and its step library
from a fork of HOL4 that moves the model to the privileged architecture 1.13 (M-mode, S-mode
and U-mode, PMP, Sv39, Sv48 and Sv57 address translation, RV64GC):

| | |
|---|---|
| Upstream | https://github.com/didriklundberg/HOL, branch `riscv-l3-smode` (S-mode and virtual memory, to be merged into branch `riscv-l3`) |
| Commit | `6d8de4304b5cc89cb29a01ff5902719af3158225` (2026-10-31) |
| Same files | every vendored file is byte-identical to its upstream counterpart at that commit; there are no local patches |
| Upstream directory | `examples/l3-machine-code/riscv/` |
| L3 version | L3-2018-02-09 (the model files are L3's HOL4 and SML exports of `src/riscv.spec`) |
| HOL4 used by HolBA | `trindemossen-2` (upstream builds the same files against HOL4 `develop`) |

The L3 source of the model, `src/riscv.spec`, is not vendored: it is in the upstream directory
at the commit above, with `src/README.md` and `src/Makefile` saying how to regenerate the
model from it. The designs are in `doc/` there: `doc/design-privileged.md` for the privileged
architecture, including the hypotheses that the M-mode step theorems carry (H1 to H6, §1.5),
and `doc/design-smode.md` for S-mode and address translation, including why the M-mode step
theorems need no hypothesis on `satp` (§1.1 to §1.3) and what HolBA lifts of it (§1.6).

## Files

| HolBA | Upstream (`examples/l3-machine-code/riscv/`) | Changed here |
|---|---|---|
| `model/riscvScript.sml` | `model/riscvScript.sml` | no |
| `model/riscvLib.sml`, `model/riscvLib.sig` | `model/riscvLib.sml`, `model/riscvLib.sig` | no |
| `model/riscv.sml`, `model/riscv.sig` | `model/riscv.sml`, `model/riscv.sig` | no |
| `step/riscv_stepScript.sml` | `step/riscv_stepScript.sml` | no |
| `step/riscv_stepLib.sml`, `step/riscv_stepLib.sig` | `step/riscv_stepLib.sml`, `step/riscv_stepLib.sig` | no |
| `step/riscv_step_selftest.sml` | `step/selftest.sml` | renamed |
| `model/Holmakefile`, `step/Holmakefile` | | HolBA's own |

Upstream's `prog/`, `decompiler/`, `sim/`, `src/` and `doc/` are not vendored. The Holmakefiles
are HolBA's: they build no heaps and find L3's `common` and `lib` directories under `$(HOLDIR)`.

## Compatibility with HOL4 `trindemossen-2`

The interfaces of HOL4 `trindemossen-2` differ from those of HOL4 `develop` in the four places
below. An earlier copy, of upstream commit `8f8ab4f20`, carried a local patch for each; upstream
applied the four patches unchanged in `37a5d7e9a`, and the commit above still has them, so the
vendored files need no local patch. Each is written so that it works with both versions:

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
not pick it up: it takes eight to ten minutes. Run it with `Holmake selftest` in `step/`; it
writes `step/riscv_step_selftest.log`. Under `trindemossen-2` it passes, with the results that
upstream reports for both HOL4 versions (`doc/design-smode.md` §1.8): it runs the step library on
the 436 entries of `riscv_dict`, the 1952 distinct instructions of upstream's `sim/tests`
programs and 46 edge cases, finds no unexpected hypothesis, gets no step theorem for `SRET`, and
finds `c_SCSR` (the S-mode CSRs) in the conclusion of 58 theorems and in no hypothesis.

## Resynchronising

1. Copy the files in the table from the new upstream commit, for example with
   `git -C <HOL fork> show <commit>:examples/l3-machine-code/riscv/<file> > <HolBA file>`.
2. Check that upstream still works with `trindemossen-2` in the four places above (and in any
   new use of an interface that differs), patch the copy where it does not, and update this
   file: commit, date, the list of local patches.
3. Build `model/` and `step/` with HolBA's HOL4 (`Holmake` in each), and run
   `Holmake selftest` in `step/`.
4. Rebuild the lifter (`src/theory/tools/lifter`, `src/tools/lifter`, the backlifter) and run
   `src/tools/lifter/selftest_riscv.sml`. A change of the step theorems shows up as a change of
   `selftest_riscv.log`; regenerate the log and check every changed block before committing it.
