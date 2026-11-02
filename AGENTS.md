# HolBA – notes for agents

## What this repository is
- The **library** (`src/`, root `holproject.toml`) provides HOL4 theories and tools for binary analysis and verification: BIR semantics, lifters, backlifters, program logics, symbolic execution, contract composition.
- How these are actually used to verify programs is shown **only in the examples**, chiefly `examples/riscv/` and `examples/arm8/`. These are separate holbuild projects that depend on the library, i.e., "client projects".
- Their `holproject.toml` files are templates for setting up other client projects that use HolBA.
- `examples/bir/` is a third client project, not about binary verification. So far it builds only `compute` (group `@compute`): "Smol BIR", an independent fragment of BIR with cv-based evaluation. Its files are prefixed `smol_bir` so that their logical names don't clash with the library's BIR theories. The other subdirectories of `examples/bir/` are not built yet.

## z3 is for clients, not for the library
- Building anything in the base library must **not** require z3, and changes must keep it that way. Don't make `src/` theories/libs call SMT at build time.
- z3 is needed only when the library is *used*, as in the examples' symbolic execution, transfer and SMT steps.
- Getting the preferred z3: `./scripts/setup/install_z3.sh` downloads z3 4.14.1 into `opt/z3-4.14.1/` (gitignored). This is one of the few legacy CI setup scripts still in regular use.
- To build examples: set `HOL4_Z3_EXECUTABLE=<repo root>/opt/z3-4.14.1/bin/z3`. Under holbuild, also set `HOLBADIR=<repo root>`, so `holba_z3Lib` finds `holba_z3Lib_prelude.z3`.

## Building
- Prefer **holbuild** (fast, incremental, resumes failed proofs from checkpoints). Holmake with `configure.sh`/`env.sh` (see README) is the legacy path.
- Run holbuild from the directory of the project you're building (repo root, `examples/riscv/`, `examples/arm8/`, or `examples/bir/`):
  - one theory: `holbuild build chacha20_double_round_propTheory`
  - a group from `[build.groups.*]`: `holbuild build @chacha20`, or `holbuild build @examples` at the root for examples under `src/`
  - no target: the project's root groups
- Example projects build against the enclosing checkout via `[overrides.holba] path = "../.."` in their `.holconfig.toml`.
- holbuild builds each theory in a staging directory and only stages files it knows a script depends on. A script that reads a non-SML file by relative path (e.g. `lift_da_and_store` reading an assembly `.da` dump) must declare it at the top of the script, or it fails with `Io ... ENOENT`:
  ```sml
  (* lets holbuild stage foo.da for the relative read below; no-op otherwise *)
  fun holbuild_extra_deps (_ : string list) = ()
  val _ = holbuild_extra_deps ["foo.da"]
  ```
  holbuild picks up the `holbuild_extra_deps [...]` call when scanning the script. The local no-op definition keeps the script valid under Holmake. Every lifted example (`<prog>Script.sml`) needs this for its `.da` file.
- Logical names must be unique across the whole holbuild build graph: all `members` directories of the project and all its dependencies (HolBA, HOL4). `fooScript.sml` has logical name `fooTheory`, while `foo.sml` and `foo.sig` both have `foo`; only a `.sig`/`.sml` pair in the same package may share one. Holmake only sees each directory's `INCLUDES`, so clashes that were harmless there fail under holbuild with `duplicate logical name`. Before adding a file, check that no other source in the project or its dependencies has the same logical name.
  - This means that a built file is unambiguously identified by its filename and project (root/`holba`, `arm8`, `riscv` or `bir`): "`isqrt_spec_arm8Script.sml` in arm8" refers to `examples/arm8/isqrt/isqrt_spec_arm8Script.sml`. Files holbuild does not build (outside `members` or excluded, e.g., `selftest.sml`, `examples/riscv/poly1305*`) are not checked and may repeat names.
- HolBA builds against a tagged HOL4 release. holbuild currently only accepts a commit SHA for `[dependencies.hol]` `rev`, so:
  - `rev` must be the commit of a HOL4 tag, i.e., `git ls-remote https://github.com/HOL-Theorem-Prover/HOL.git 'refs/tags/<tag>^{}'`, not the annotated tag object's own SHA.
  - The root `holproject.toml` names the tag in a comment above `rev`.
  - All `holproject.toml` files (root, `examples/arm8`, `examples/riscv`, `examples/bir`) use the same `rev`; change them together.
- `.holconfig.toml` settings are **not** inherited between projects: `[build]` options such as `jobs` and `checkpoint_limit_gb` must be repeated in each project.
- Poly/ML: use 5.9.2. Ubuntu's packaged 5.7.1 (still mentioned in the README) has been associated with intermittent deadlocks when spawning z3.
- Changing a library file (e.g. `bir_symbLib`, `bir_riscv_backlifterTheory`) rebuilds every dependent example. Symbolic execution and transfer theories are the slow part.

## Iterating on proofs using holbuild with a short tactic timeout
- The default tactic timeout is 600s (`tactic_timeout`), so a looping `simp`/`rw` costs 10 min. When developing proofs, use `--tactic-timeout N` (e.g. 30–120) so a bad tactic fails fast.
- The reuse behaviour below was observed with **holbuild 0.12.0**. It differed in 0.11.0, and holbuild changes quickly, so recheck it after upgrading (`holbuild --version`).
- Built theories record the timeout they were built under. This holds for both cache entries and local objects in `.holbuild/obj`. A theory built under timeout T is reused only by builds whose timeout is at least T.
  - So a short-timeout build of a goal theory also rebuilds every project theory it depends on that was built at the regular timeout. Building the dependencies first at the regular timeout does not prevent this. Dependency packages such as HolBA in `.holbuild/packages/holba` were not rebuilt.
  - Later short-timeout iterations reuse those rebuilt theories, and so does the next regular build, which then has nothing to do.
  - The cost is one extra build of the project chain, e.g. about 3.5 min for `isqrt_propTheory`. If some dependency has a tactic slower than N, that rebuild fails. Then pick a larger N.
- Never pass `--tactic-timeout` to a broad target (`@group`, no target) or in a project whose `.holbuild` is cold (e.g. the repo root when only the examples have been built: they build HolBA in their own `.holbuild/packages/holba`). That rebuilds everything without cache.

## Long builds and hangs
- Durations vary widely on modern 8+ multicore machines:
  - small arm8 examples: about 1–2 min each
  - riscv chacha20 chain: about 10 min (z3 heavy)
  - `examples/arm8/aes/wp` (excluded from the build): `aesWpsTheory` and `aesM0WpsTheory` ran for about 1.5 h without finishing (~15 of ~70 labels left), each peaking above 20 GB of memory. Labels slow down as the wp expressions grow, from several per minute to under one per 10 min. Whether they ever finish is unknown.
  - from scratch (HOL + HolBA + one example): about 25 min
- A quiet log is not a hang. Judge progress by CPU-time deltas of `hol`/`z3` (`/proc/PID/stat` fields 14+15), not by `ps %CPU`, which is a lifetime average. z3 busy while `hol` waits is progress.
- Known hang patterns:
  - a child `hol` with zero CPU that never exec'd z3 (fork-before-exec deadlock)
  - a holbuild child with no HOL process under it
- Before killing a hang: capture a backtrace (`gdb -p PID -batch -ex "thread apply all bt"`) and the Poly/ML and holbuild versions. Then kill the holbuild process tree and rerun; cached work resumes.

## Code layout
- `src/theory/`: BIR semantics, program logic (`program_logic/`: `t_jgmt`, `t_ext_jgmt`, `transition_system`), backlifter theories.
- `src/tools/`: lifter, backlifter (`get_riscv_contract_thm` / `get_arm8_contract_thm`), symbolic execution (`bir_symbLib`), composition (`bir_compositionLib`).
- Verification pipeline in a client project (e.g. `examples/riscv/chacha20`), per code fragment:
  1. `<prog>Script`: lift the binary
  2. `*_spec_riscv`: addresses, RISC-V pre/postconditions
  3. `*_spec_bir`: BIR pre/postconditions, plus RISC-V⇒BIR lemmas
  4. `*_symb_exec`: symbolic execution
  5. `*_symb_transf`: transfer to `bir_cont` (SMT-heavy)
  6. `*_prop`: backlift to `riscv_cont`, final massaging to the desired spec
- `examples/arm8/tutorial/` walks through the whole pipeline, including contract composition (step 7).

## Where general code goes
- Examples should only prove things specific to their program and specification. Move general results into the library (it is fine to develop them in an example first).
- Contract rules (consequence, subset, sequencing, loops, ...) belong next to the contract definitions:
  - `arm8_cont`: `src/theory/tools/backlifter/bir_arm8_backlifterScript.sml`
  - `riscv_cont`: `src/theory/tools/backlifter/bir_riscv_backlifterScript.sml`
- General tactics and rules that are not specific to BIR (e.g. `QINST_IRULE`, `QSPECL_ASSUM`) belong in `src/extra/holba_auxiliaryLib.sml` (and its `.sig`).
- Changing these files rebuilds most of the library and all examples (a `holba_auxiliaryLib.sig` change took ~20 min for the arm8 examples), so batch such changes.

## Contract reasoning
- `riscv_cont`/`t_jgmt` are total-correctness, **first-encounter** judgments: the post holds at the first label reached from the ending set.
  - So sequential composition needs the first contract to also list the second contract's end label(s), with postcondition `false`.
  - See `bir_symb_transfer_excl` and `riscv_cont_seq_rule`.
  - Symbolic transfer can only exclude labels outside the analysed fragment, and a fragment's own start label is always inside. So no fragment contract can show that a loop iteration reaches the loop head *first*, which the standard loop rule (`total_loop_rule_thm`) requires. This holds for both arm8 and riscv.
  - Instead, use a loop rule over avoidance contracts, which only require that the loop exit is not encountered before returning to the head. arm8: `arm8_cont_avoid` and `arm8_cont_loop_rule`, used in `examples/arm8/isqrt`. riscv: `riscv_cont_avoid` and `riscv_cont_loop_rule`, which mirror the arm8 rules.
  - Avoidance contracts come from ordinary contracts via `*_cont_avoid_intro`, and compose with `*_cont_avoid_seq_rule` / `*_cont_avoid_cont_seq_rule`.
  - Templates: small loop-free code can be one fragment (`examples/arm8/update_sat`). For loops, fragments cut at the loop head, so that no symbolic execution runs around the loop, composed with the loop rule (`examples/arm8/isqrt`, `examples/arm8/add_reg`).
  - Symbolic execution and transfer scale poorly with fragment size; large symbolic states can make z3 blow up. So if scaling has been determined to be a likely problem, split larger loop-free code into fragments too, and compose their contracts with the sequencing rules.
  - Choose the loop head where the loop condition is a predicate on registers, e.g., before the `cmp`, not at the conditional branch, where it only exists in the flags.
- Run each symbolic execution/transfer once, producing the strongest contract needed. Derive weaker variants in `*_prop` with `riscv_cont_subset_rule` / `riscv_cont_conseq_rule` (arm8: `arm8_cont_subset_rule` / `arm8_cont_conseq_rule`). `*_spec_*` theories may contain such auxiliary, stronger specifications.
- Write labels in contracts and their supporting lemmas as the named address definitions from `*_spec_<arch>` (e.g. `isqrt_end_addr_2`, `chacha20_column_round_end_addr`), not hex literals. This covers `arm8_cont`/`riscv_cont` statements, PC conditions in pre/postconditions, and label cases (`BL_Address (Imm64 ...)`) in BIR postcondition lemmas.
  - The BIR contracts from symbolic transfer (`bspec_cont_*`) contain the hex values. Backlift with `get_riscv_contract_thm` / `get_arm8_contract_thm`, which take the address definitions and state the result with the names. `get_riscv_contract` / `get_arm8_contract` are legacy.
  - If a BIR postcondition lemma names labels, also pass the address definitions in the `bir_post_defs` argument, so that it matches the hex labels of the BIR contract (see `examples/riscv/chacha20/chacha20_column_round_propScript.sml`).
- Write BIR terms (e.g. the BIR pre/postconditions in `*_spec_bir`) with `bslSyntax` constructors (`beq`, `bden`, `bconst`, `bplus`, `bandl`, ...), not raw BIR abstract syntax (`BExp_BinPred BIExp_Equal (BExp_Den (BVar ...)) ...`). This limits verbosity and makes the terms clearer. Examples: `examples/arm8/update_sat/update_sat_spec_birScript.sml`, `examples/arm8/isqrt/isqrt_spec_birScript.sml`.
  - Longer term, the aim is to remove the need to write explicit BIR in contract proof files at all.
  - Until then, `*_spec_bir` should, as a rule, be an explicit record of the BIR counterpart of each `*_spec_<arch>` contract condition. Write one clause per conjunct of the RISC-V/arm8 condition, in the same order, so the two can be read side by side. Don't generate clauses (e.g. with `List.tabulate`/`List.map` over registers or offsets) or hide them behind non-`bslSyntax` helper functions.

## What arm8 and riscv examples prove, and what is trusted
- The output of a typical binary verification example in `examples/arm8/` or `examples/riscv/` is an ISA-level contract theorem in its `*_prop` theory (e.g. `riscv_cont_kernel_trap_entry`, `arm8_cont_isqrt`). Its `*_full` variant unfolds the contract into a statement about the L3 ISA model alone: the step function `NextRISCV` / `NextStateARM8` (`bmr_step_fun` in `bir_lifting_machinesTheory`) running the program bytes (`*_progbin`) in memory.
- Trusting a folded ISA contract theorem requires trusting the L3 model of the corresponding ISA, the general contract definitions (`riscv_cont`/`arm8_cont`, `t_jgmt`), the `*_spec_<arch>` pre/postconditions with their address definitions, and the program bytes (generated from the `.da` file).
- BIR language definitions and BIR expressions do not appear in any ISA contract theorem. The lifter, `*_spec_bir`, symbolic execution and transfer are intermediate proof devices that don't need to be trusted if one trusts the HOL4 kernel.
- The exception is the conversion from BIR to SMT, which **is** part of the trusted base.
  - Symbolic execution and transfer ask z3 about BIR expressions, e.g., implications, path-condition contradictions and transfer side conditions.
  - They turn z3's answers into theorems with `mk_oracle_thm`: tags `BIRS_IMP_Z3` and `BIRS_CONTR_Z3` in `src/tools/symbexec/birs_utilsLib.sml`, `BIRS_TRANSF_LIB_Z3` in `distribute_generic_stuffLib.sml`, all via `bir_smtLib`.
  - These oracle theorems state facts about BIR semantics. So the final theorem can be trusted only if z3 is sound and the BIR-to-SMT-LIB translation (`src/shared/smt/`, including `holba_z3Lib_prelude.z3`) agrees with BIR expression semantics.
  - The final example theorems carry these tags. Check with `Tag.dest_tag (Thm.tag th)` (`DISK_THM` only marks theorems loaded from disk).
- Consequences for auditing changes to examples and the library:
  - The trusted part is the conversion mechanism, not its inputs. BIR expressions used in contract proof (typically in `*_spec_bir`) only affect what is sent to z3. So changes to them that keep the build passing need no semantic review, even if they change the BIR terms, as long as the mechanism is unchanged.
  - Changes to a contract statement, `*_spec_<arch>`, the L3 model, or anything else the `*_full` statement depends on do.
  - So do changes to the BIR-to-SMT conversion or to where the oracles are invoked.

## Git
- Main branch is `master`.
- Never commit `.holbuild/` or `opt/`, or any `.hol/` directory.
