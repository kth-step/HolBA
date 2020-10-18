# HolBA - Binary analysis in HOL 

Be sure to check out the Wiki, which contains some useful general information about HolBA.

## Software versions

- HOL4 (`https://github.com/HOL-Theorem-Prover/HOL`)
  - tag: kananaskis-13
- Poly/ML (e.g. current Poly/ML version packaged for Ubuntu, 5.7.1)
- Z3 v4.8.4

## How to setup and compile

The directory scripts/setup contains a relatively flexible set of shell scripts to help with the initial setup. The most simple setup can be done with a few shell commands and requires no manual dealing with environment variables. More sophisticated setups allow convenient sharing of the required software packages and setup environment variables in a custom shell script.

### Simple setup
```bash
git clone https://github.com/kth-step/HolBA.git
cd HolBA

# This sets up all dependencies in this HolBA
# directory ({HOLBA_DIR}/opt). It downloads and
# builds polyml and HOL4 for example.
./scripts/setup/install_all.sh

# In order to create a configuration file with
# the directories for the installed tools,
# execute the following line
./configure.sh

# For convenience and indepence of make, this command
# augments the environment with ${HOLBA_*} variables
# as well as the ${PATH} variable. Now calls to Holmake
# use the installed instance of HOL4 in the opt directory.
# Furthermore, some tools require these variables to
# run properly. It has to be run for each new shell.
source env.sh

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

* You can use `make --directory=${HOLBA_DIR} rulename`.


### More advanced setup with shared dependencies and `~/.bashrc`

For this you need to:
1. Prepare a HolBA directory with the setup scripts: `{HOLBA_DIR}`.
1. Select a directory where you want to install and place the shared dependencies: `{HOLBA_OPT_DIR}`.
1. Add the following to your `~/.bashrc` file:
```bash
export HOLBA_OPT_DIR=/path/to/{HOLBA_OPT_DIR}
```
1. Start a new shell and run these shell commands:
```bash
cd /path/to/{HOLBA_DIR}
./scripts/setup/install_base.sh
./configure.sh
make main
```

Notice that this sequence is exemplary and it is possible to selectively run the `install_*.sh` scripts for the components that are desired. The script `config.env.sh` is generated and contains all variables for components which can be found in `${HOLBA_OPT_DIR}` or are available in the shell when `./configure.sh` runs. Sourcing the script `./env.sh` in the respective copy of the HolBA repository will setup the currently running shell for development there.



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
  * works for small programs
  * cannot handle certain cases, like memory dependent observations
  * includes a selection of cache side channel models

### Dependency graph

![Dependency diagram](./doc/diagrams/dependencies.png?raw=true)

Key:
 - Blue edges represent dependencies between HolBA modules.

### PolyML heaps

- The heap chain is no longer represented in the diagram. You can see it by
  reading the `Holmakefile.gen` files.
- See HOL's Description Manual for more information about PolyML heaps.
- You can temporarily change the heap chain order if you don't need a dependency
  in order to reduce build times.



## References

* A. Lindner, R. Guanciale and R. Metere, **"TrABin : Trustworthy analyses of binaries"**, Science of Computer Programming, vol. 174, p. 72-89, 2019. [Link](https://doi.org/10.1016/j.scico.2019.01.001). _(the proof-producing binary analysis framework with weakest preconditions in HOL4)_

* D. Lundberg, **"Provably Sound and Secure Automatic Proving and Generation of Verification Conditions"**, Master Thesis, 2018. [Link](http://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Akth%3Adiva-239441).

* R. Metere, A. Lindner and R. Guanciale, **"Sound Transpilation from Binary to Machine-Independent Code"**, in 20th Brazilian Symposium on Formal Methods, p. 197-214, 2017. [Link](https://doi.org/10.1007/978-3-319-70848-5_13). _(formalization of intermediate language and proof-producing lifter in HOL4)_

* D. Lundberg, R. Guanciale, A. Lindner and M. Dam, **"Hoare-Style Logic for Unstructured Programs"**, in Software Engineering and Formal Methods, p. 193-213, 2020. [Link](https://doi.org/10.1007/978-3-030-58768-0_11). _(program logic used for decomposition of verification)_



