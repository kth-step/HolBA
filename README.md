# Software versions

- HOL4 (`https://github.com/kth-step/HOL`)
  - branch: for_holba (i.e. tags/kananaskis-12 + holsmt-arrays + syntax-errors)
- Poly/ML (e.g. current Poly/ML version packaged for Ubuntu, 5.7.1)


# How to compile

* First, run `make [main|examples|benchmarks|...]` in the root directory,
  according to your needs.
* Then, go into the directory you want to use and run `{HOLDIR}/bin/Holmake`.
* If one of the previous steps fails, try to clean your Git working directory by
  `make cleanslate` in the project root directory. **Be careful though**, this
  command is quite dangerous as it can easily eat your files (`Holmakefile`s are
  auto-generated from `Holmakefile.gen` files, so they are removed by this
  command).


# Branch policy

### `master` branch

`master` is the standard branch where **completed features** are merged:
 - no cheat
 - must correctly compile
 - self tests must succeed
 - code should be tested
 - bug-fixes are ok
 - 1 review is needed in order to merge into `master`

Follow these instructions whenever you merge to master:
  - `grep` for "cheat"
  - check that the `README` is up to date (especially tool status)
  - find a reviewer for your Pull Request

### `dev` branch

`dev` is the branch where every feature is available, but not necessarily finalized:
  - Can cheat
  - Code can be commented out
  - **Holmake must work**
  - bug-fixes are ok

However, **no development happens on this branch**, but rather on separate
feature branches.

**In order to prevent mayhem**, define good interfaces for your code, so that
development won't break existing code.

### Feature branches

Every "somewhat" working tool should be available in the `dev` branch, but new
features or any development must go on new branches.
 - branch names must be short and explicit (prefer explicit over short)
 - every feature branch should involve small developments
 - rebase feature branches on `dev` **often**, by using `git rebase` or `git merge`
 - **merge feature branches on `dev` often**: work on small features

Some rules for feature branches:
 - commits in a feature branch must compile, unless explicitly stated in commit
   message (with the prefix `[WIP] ...` for instance)
 - further subbranch to do implementation experiments (keep them small)

If you want to violate the rules for temporary development or experiments (only
for feature branches):
  1. Fork
  2. Do a good mess
  3. Merge in feature branch after history rewrite


# Folders and organization

```
├─ doc
└─ src
   ├─ core: core BIR language
   ├─ libs: general BIR libraries, used by tools
   │  └─ examples: Examples showcasing the use of libs/ libraries.
   ├─ theories: various supporting theories
   ├─ tools
   │  ├─ cfg: Control Flow Graph utilities
   │  │  └─ examples: CFG-related small examples
   │  ├─ exec: concrete execution
   │  │  └─ examples: concrete execution-related small examples
   │  ├─ lifter: proof-producing binary lifter
   │  │  ├─ benchmark
   │  │  └─ examples: lifter-related small examples
   │  ├─ pass: Passification utility
   │  │  └─ examples: Passification-related small examples
   │  └─ wp: weakest precondition propagation
   │     ├─ benchmark
   │     └─ examples: WP-related small examples
   └─ examples: to showcase HolBA features
```

Tools status:
- `tools/cfg`:
  * non proof-producing
  * no clear interface yet
  * GraphViz exporter working
- `tools/exec`:
  * proof-producing
  * unstable BIR evaluation utilities
  * quite easy to use
- `tools/lifter`:
  * merged in `master` => very stable
  * proof-producing
  * widely used in examples
  * supports: ARMv8, Cortex-M0
- `tools/wp`:
  * proof-producing
  * experimental implementation
    * includes prototype of substitution simplification
  * interface in progress
- `tools/pass`:
  * non proof-producing
  * experimental passification transformation to SSA


# Coding style

* HOL source code
  - Spaces, no tabs
  - No unicode
  - `snake_case` (e.g. `bir_number_of_mem_splits_def`)
