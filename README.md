# HolBA - Binary analysis in HOL 

## Software versions

- HOL4 (`https://github.com/kth-step/HOL`)
  - branch: for_holba (i.e. tags/kananaskis-12 + holsmt-arrays + syntax-errors)
- Poly/ML (e.g. current Poly/ML version packaged for Ubuntu, 5.7.1)
- Z3 v4.8.4


## How to setup and compile

The directory scripts/setup contain a relatively flexible set of shell scripts to help with the initial setup. The most simple setup can be done with a few shell commands and require no manual dealing with environment variables. More sophisticated setups allow convenient sharing of the required software packages and setup environment variables in a custom shell script.

### Simple setup
```bash
git clone https://github.com/kth-step/HolBA.git
cd HolBA

# This sets up all dependencies in this HolBA
# directory ({HOLBA_DIR}/opt). It downloads and
# builds polyml and HOL4 for example.
./scripts/setup/install_all.sh

# For convenience and indepence of make, this command
# augments the environment with ${HOLBA_*} variables
# and allows calls to ${HOLBA_HOLMAKE} for example.
# Some tools require these variables to run properly.
# It has to be run for each new shell.
source ./scripts/setup/autoenv.sh

# This prints the available convenience
# rules like tests and examples.
make

# This builds HolBA.
make main
make tests

# Specific directories can be built using make, ...
make examples/aes

# ... or manually
cd examples/aes
${HOLBA_HOLMAKE}
```

### General notes

* If one of the previous steps fails, try to clean your Git working directory by
  `make cleanslate` in the project root directory. **Be careful though**, this
  command is quite dangerous as it can easily eat your files (`Holmakefile`s are
  auto-generated from `Holmakefile.gen` files, so they are removed by this
  command).

* You can use `make --directory=${HOLBA_DIR} rule`.


### More advanced setup with shared dependencies and `~/.bashrc`

For this you need to:
1. Prepare a HolBA directory with the setup scripts: `{HOLBA_DIR}`.
1. Select a directory where you want to install and place the shared dependencies: `{HOLBA_OPT_DIR}`.
1. Run these shell commands:
```bash
cd /path/to/{HOLBA_DIR}
./scripts/setup/install_base.sh
./scripts/setup/install_mk_env.sh
```
1. Add the following to your `~/.bashrc` file:
```bash
export HOLBA_OPT_DIR=/path/to/{HOLBA_OPT_DIR}

source ${HOLBA_OPT_DIR}/env.sh
```
1. Start a new shell and compile HolBA by using `make main`.

Notice that this sequence is exemplary and it is possible to selectively run the `install_*.sh` scripts for the components that are desired. The script `${HOLBA_OPT_DIR}/env.sh` is generated and contains all variables for components which can be found in `${HOLBA_OPT_DIR}` or are available in the shell when `install_mk_env.sh` runs.


## Branch policy

### tags

tags should have as many **completed features** as possible:
 - no cheat
 - must correctly compile
 - self tests must succeed
 - code should be tested

Follow these instructions whenever you merge to master:
  - `grep` for "cheat"
  - check that the `README` is up to date (especially tool status)
  - find a reviewer for your Pull Request

### `master` branch

`master` is the branch where every feature is available, but not necessarily finalized:
  - Can cheat, but has to be avoided
  - Code should not be be commented out
  - **Holmake must work**
  - bug-fixes are ok
  - 1 review is needed in order to merge into `master`

However, **no development happens on this branch**, but rather on separate
feature branches.

**In order to prevent mayhem**, define good interfaces for your code, so that
development won't break existing code.

### Feature branches

Every "somewhat" working tool should be available in the `master` branch, but new
features or any development must go on new branches prefixed with `dev_`.
 - branch names must be short and explicit (prefer explicit over short)
 - every feature branch should involve small developments
 - rebase feature branches on `master` **often**, by using `git rebase` or `git merge`
 - **merge feature branches on `master` often**: work on small features

Some rules for feature branches:
 - commits in a feature branch must compile, unless explicitly stated in commit
   message (with the prefix `[WIP] ...` for instance)
 - further subbranch to do implementation experiments (keep them small)

If you want to violate the rules for temporary development or experiments (only
for feature branches):
  1. Fork
  2. Do a good mess
  3. Merge in feature branch after history rewrite


## Folders and organization

```
├─ doc
├─ src
│  ├─ theory
│  │  ├─ bir: core BIR language
│  │  ├─ bir-support: various supporting theories for bir
│  │  ├─ models: various machine models
│  │  └─ tools: theories used by the tool libraries in src/tools
│  │     ├─ ...
│  │     ...
│  ├─ shared: general BIR libraries, used by libraries in tools
│  └─ tools
│     ├─ cfg: Control Flow Graph utilities
│     ├─ exec: concrete execution
│     ├─ lifter: proof-producing binary lifter
│     ├─ pass: Passification utility
│     ├─ wp: weakest precondition propagation
│     └─ scamv: abstract side channel model validation framework
└──── examples: to showcase HolBA
```

### Tools status:

- `tools/cfg`:
  * non proof-producing
  * no clear interface yet
  * GraphViz exporter working
- `tools/exec`:
  * proof-producing
  * unstable BIR evaluation utilities (no clear interface yet)
  * quite easy to use
- `tools/lifter`:
  * very stable
  * proof-producing
  * widely used in examples
  * supports: ARMv8, Cortex-M0, Cortex-M0 with clock cycke counter
- `tools/wp`:
  * proof-producing
  * experimental implementation
    * includes prototype of substitution simplification
  * interface in progress
- `tools/pass`:
  * non proof-producing
  * experimental passification transformation to SSA
- `tools/scamv`:
  * experimental and under development

### Dependency graph

![Dependency diagram](./doc/diagrams/dependencies.png?raw=true)

Key:
 - Blue edges represent dependencies between HolBA modules.

### PolyML heaps

- The heap chain is no longer represented in the diagram. You can see it by
  reading the `Holmakefil.gen` files.
- See HOL's Description Manual for more information about PolyML heaps.
- You can temporarily change the heap chain order if you don't need a dependency
  in order to reduce build times.

## Coding style

* HOL source code
  - Spaces, no tabs
  - No unicode
  - `snake_case` (e.g. `bir_number_of_mem_splits_def`)
