# HolBA – notes for agents

## What this repository is
- The **library** (`src/`, root `holproject.toml`) provides HOL4 theories and tools for binary analysis and verification: BIR semantics, lifters, backlifters, program logics, symbolic execution, contract composition.
- How these are actually used to verify programs is shown **only in the examples**, chiefly `examples/riscv/` and `examples/arm8/`. These are separate holbuild projects that depend on the library, i.e., "client projects".
- Their `holproject.toml` files are templates for setting up other client projects that use HolBA.

## z3 is for clients, not for the library
- Building anything in the base library must **not** require z3, and changes must keep it that way. Don't make `src/` theories/libs call SMT at build time.
- z3 is needed only when the library is *used*, as in the examples' symbolic execution, transfer and SMT steps.
- Getting the preferred z3: `./scripts/setup/install_z3.sh` downloads z3 4.14.1 into `opt/z3-4.14.1/` (gitignored). This is one of the few legacy CI setup scripts still in regular use.
- To build examples: set `HOL4_Z3_EXECUTABLE=<repo root>/opt/z3-4.14.1/bin/z3`. Under holbuild, also set `HOLBADIR=<repo root>`, so `holba_z3Lib` finds `holba_z3Lib_prelude.z3`.

## Building
- Prefer **holbuild** (fast, incremental, resumes failed proofs from checkpoints). Holmake with `configure.sh`/`env.sh` (see README) is the legacy path.
- Run holbuild from the directory of the project you're building (repo root, `examples/riscv/`, or `examples/arm8/`):
  - one theory: `holbuild build chacha20_double_round_propTheory`
  - a group from `[build.groups.*]`: `holbuild build @chacha20`, or `holbuild build @examples` at the root for examples under `src/`
  - no target: the project's root groups
- Example projects build against the enclosing checkout via `[overrides.holba] path = "../.."` in their `.holconfig.toml`.
- `.holconfig.toml` settings are **not** inherited between projects: `[build]` options such as `jobs` and `checkpoint_limit_gb` must be repeated in each project.
- Poly/ML: use 5.9.2. Ubuntu's packaged 5.7.1 (still mentioned in the README) has been associated with intermittent deadlocks when spawning z3.
- Changing a library file (e.g. `bir_symbLib`, `bir_riscv_backlifterTheory`) rebuilds every dependent example. Symbolic execution and transfer theories are the slow part.

## Iterating on proofs using holbuild with a short tactic timeout
- The default tactic timeout is 600s (`tactic_timeout`), so a looping `simp`/`rw` costs 10 min. When developing proofs, use `--tactic-timeout N` (e.g. 30–120) so a bad tactic fails fast.
- Cache entries record the timeout they were built under; a different `--tactic-timeout` makes them unusable and forces rebuilds. Up-to-date local objects in the project's `.holbuild/obj` are still reused.
- So leverage the cache first, then apply the short timeout only to the goal file:
  1. build its dependencies with the regular timeout, e.g. `holbuild build isqrt_symb_transfTheory`
  2. iterate with `holbuild build --tactic-timeout 30 isqrt_propTheory`
- Never pass `--tactic-timeout` to a broad target (`@group`, no target) or in a project whose `.holbuild` is cold (e.g. the repo root when only the examples have been built: they build HolBA in their own `.holbuild/packages/holba`). That rebuilds everything without cache.
- Theories built under the short timeout are rebuilt once by the next regular build; this is cheap for small theories.

## Long builds and hangs
- Durations vary widely on modern 8+ multicore machines:
  - small arm8 examples: about 1–2 min each
  - riscv chacha20 chain: about 10 min (z3 heavy)
  - from scratch (HOL + HolBA + one example): about 25 min
- A quiet log is not a hang. Judge progress by CPU-time deltas of `hol`/`z3` (`/proc/PID/stat` fields 14+15), not by `ps %CPU`, which is a lifetime average. z3 busy while `hol` waits is progress.
- Known hang patterns:
  - a child `hol` with zero CPU that never exec'd z3 (fork-before-exec deadlock)
  - a holbuild child with no HOL process under it
- Before killing a hang: capture a backtrace (`gdb -p PID -batch -ex "thread apply all bt"`) and the Poly/ML and holbuild versions. Then kill the holbuild process tree and rerun; cached work resumes.

## Code layout
- `src/theory/`: BIR semantics, program logic (`program_logic/`: `t_jgmt`, `t_ext_jgmt`, `transition_system`), backlifter theories.
- `src/tools/`: lifter, backlifter (`get_riscv_contract`), symbolic execution (`bir_symbLib`), composition (`bir_compositionLib`).
- Verification pipeline in a client project (e.g. `examples/riscv/chacha20`), per code fragment:
  1. `<prog>Script`: lift the binary
  2. `*_spec_riscv`: addresses, RISC-V pre/postconditions
  3. `*_spec_bir`: BIR pre/postconditions, plus RISC-V⇒BIR lemmas
  4. `*_symb_exec`: symbolic execution
  5. `*_symb_transf`: transfer to `bir_cont` (SMT-heavy)
  6. `*_prop`: backlift to `riscv_cont`, final massaging to the desired spec
- `examples/arm8/tutorial/` walks through the whole pipeline, including contract composition (step 7).

## Contract reasoning
- `riscv_cont`/`t_jgmt` are total-correctness, **first-encounter** judgments: the post holds at the first label reached from the ending set.
  - So sequential composition needs the first contract to also list the second contract's end label(s), with postcondition `false`.
  - See `bir_symb_transfer_excl` and `riscv_cont_seq_rule`.
- Run each symbolic execution/transfer once, producing the strongest contract needed. Derive weaker variants in `*_prop` with `riscv_cont_subset_rule` / `riscv_cont_conseq_rule`. `*_spec_*` theories may contain such auxiliary, stronger specifications.

## Git
- Main branch is `master`. The HOL4 revision is pinned in `holproject.toml`.
- Never commit `.holbuild/` or `opt/`.
