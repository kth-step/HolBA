# HolBA - Binary analysis in HOL 

[![Build Status](https://github.com/kth-step/HolBA/workflows/CI%20Build/badge.svg?branch=master)](https://github.com/kth-step/HolBA/actions?query=workflow%3A%22CI+Build%22)

Be sure to check out the Wiki, which contains some useful general information about HolBA.

## How to setup and compile

The directory scripts/setup contains a relatively flexible set of shell scripts to automate the setup. The most simple setup can be done with a few shell commands and does not require manually installing dependencies and dealing with environment variables. More sophisticated setups allow convenient sharing of the required software packages and setup environment variables in a custom shell script.

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

### Software versions

- HOL4, tag `kananaskis-14` (`https://github.com/HOL-Theorem-Prover/HOL`).
  If you download it yourself, be sure to fix problems with modern C++
  compilers by running the following commands in your HOL4 root directory
  before you run `./bin/build`:
  ```shell
  sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' src/HolSat/sat_solvers/minisat/Makefile
  sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' src/HolSat/sat_solvers/zc2hs/Makefile
  ```
- Poly/ML 5.9
  - alternatively, Poly/ML 5.7.1 (version packaged for Ubuntu 20.04)
- Z3 v4.8.4


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

Notice that this sequence is just an example, and it is possible to selectively run the `install_*.sh` scripts for the components that are desired. The script `config.env.sh` is generated and contains all variables for components which can be found in `${HOLBA_OPT_DIR}` or are available in the shell when `./configure.sh` runs. Sourcing the script `./env.sh` in the respective copy of the HolBA repository will setup the currently running shell for development there.



## Folders and organization

```
├─ doc: Documentation material
├─ examples: Showcasing HolBA
│  ├─ aes: lifting + WP of AES on ARMv8 and for Cortex-M0
│  ├─ bsl-wp-smt: Small BIR example programs to test simplified BIR generation, WP propagation and SMT interface
│  ├─ nic: NIC formalization
│  ├─ tutorial: End-to-end tutorial of simple ARMv8 examples
├─ scripts: CI and installation scripts
└─ src
   ├─ aux: Non-HolBA-specific theories and libraries
   ├─ shared: Libraries shared between tools
   ├─ theory
   │  ├─ abstract-hoare-logic: Abstract Hoare-style logic for unstructured code
   │  ├─ bir: Core BIR language
   │  ├─ bir-support: Extensions and supporting theories for BIR
   │  ├─ models: Additional machine models
   │  └─ tools: Theories for the tool libraries in src/tools
   └─ tools
      ├─ backlifter: Gets ISA-level contracts from BIR contracts
      ├─ cfg: Control Flow Graph utilities
      ├─ comp: Composition of contracts
      ├─ exec: Concrete execution
      ├─ lifter: Transpiler from binary to BIR
      ├─ pass: Passification utility
      ├─ scamv: Abstract side channel model validation framework
      └─ wp: Weakest precondition propagation
```

### Tools status:

- `tools/backlifter`:
  * Proof-producing
  * Clear interface
  * Experimental implementation
- `tools/cfg`:
  * Non-proof-producing
  * No clear interface yet
  * GraphViz exporter working
- `tools/comp`:
  * Proof-producing
  * Decent interface
  * Experimental implementation
  * Requires documentation
- `tools/exec`:
  * Proof-producing
  * Unstable BIR evaluation utilities (no clear interface yet)
  * Quite easy to use
- `tools/lifter`:
  * Proof-producing
  * Very stable
  * Widely used in examples
  * Supports: ARMv8, Cortex-M0, Cortex-M0 with clock cycle counter, RISC-V
- `tools/pass`:
  * Non-proof-producing
  * Experimental passification transformation to SSA
- `tools/scamv`:
  * Works for small programs
  * Includes a selection of cache side channel models
- `tools/wp`:
  * Proof-producing
  * Interface in progress
  * Fairly stable
  * Includes prototype of substitution simplification

### PolyML heaps

- The heap chain is no longer represented in the diagram. You can see it by
  reading the `Holmakefile.gen` files.
- See HOL's Description Manual for more information about PolyML heaps.
- You can temporarily change the heap chain order if you don't need a dependency
  in order to reduce build times.

## References

* D. Lundberg, R. Guanciale, A. Lindner and M. Dam, **"Hoare-Style Logic for Unstructured Programs"**, in Software Engineering and Formal Methods, pp. 193-213, 2020. [Link](https://doi.org/10.1007/978-3-030-58768-0_11). _(program logic used for decomposition of verification)_

* H. Nemati, P. Buiras, A. Lindner, R. Guanciale and S. Jacobs, **"Validation of Abstract Side-Channel Models for Computer Architectures"**, in International Conference on Computer Aided Verification, pp. 225-248, 2020. [Link](https://doi.org/10.1007/978-3-030-53288-8_12). _(framework to validate abstract side-channel models)_

* A. Lindner, R. Guanciale and R. Metere, **"TrABin : Trustworthy analyses of binaries"**, Science of Computer Programming, vol. 174, pp. 72-89, 2019. [Link](https://doi.org/10.1016/j.scico.2019.01.001). _(the proof-producing binary analysis framework with weakest preconditions in HOL4)_

* D. Lundberg, **"Provably Sound and Secure Automatic Proving and Generation of Verification Conditions"**, Master Thesis, 2018. [Link](http://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Akth%3Adiva-239441).

* R. Metere, A. Lindner and R. Guanciale, **"Sound Transpilation from Binary to Machine-Independent Code"**, in 20th Brazilian Symposium on Formal Methods, pp. 197-214, 2017. [Link](https://doi.org/10.1007/978-3-319-70848-5_13). _(formalization of intermediate language and proof-producing lifter in HOL4)_
