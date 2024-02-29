# HolBA - Binary analysis in HOL 

[![Build Status](https://github.com/kth-step/HolBA/workflows/CI%20Build/badge.svg?branch=master)](https://github.com/kth-step/HolBA/actions?query=workflow%3A%22CI+Build%22)

HolBA is a library based on the HOL4 theorem prover that provides
tools for analysis and formal proofs of properties of programs in binary
format that use the ARMv8, RISC-V and Cortex-M0 instruction sets.

## Building

HolBA is built using the `Holmake` tool bundled with HOL4.

### Dependencies

- [HOL4](https://github.com/HOL-Theorem-Prover/HOL), tag `kananaskis-14`.
  If you download HOL4 yourself, be sure to fix problems with modern C++
  compilers by running the following commands in your HOL4 root directory
  before you run `./bin/build`:
  ```shell
  sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' src/HolSat/sat_solvers/minisat/Makefile
  sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' src/HolSat/sat_solvers/zc2hs/Makefile
  ```
- [Poly/ML](https://github.com/polyml/polyml), 5.9
  - alternatively, Poly/ML 5.7.1 (version packaged for Ubuntu 20.04)
- [Z3](https://github.com/Z3Prover/z3), 4.8.4

### Build using existing HOL4 installation

If you already have HOL4 installed and `Holmake` in your path,
you can do the following to build the whole library, excluding examples:

```bash
git clone https://github.com/kth-step/HolBA.git
cd HolBA
Holmake
```

To build examples, you need to set the path to the Z3
binary and then run `Holmake` in the `examples` directory:

```bash
export HOL4_Z3_EXECUTABLE=/path/to/z3
cd examples
Holmake
```

### Build from scratch

For convenience, HolBA provides some scripts to bootstrap
an environment with HOL4 and Z3 from a bash shell.

```bash
git clone https://github.com/kth-step/HolBA.git
cd HolBA

# This sets up all dependencies in this HolBA
# directory (${HOLBA_DIR}/opt). It downloads and
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

# This builds the whole library, excluding examples
${HOLBA_HOLMAKE}

# This builds the examples
cd examples
${HOLBA_HOLMAKE}
```

## Directories and organization

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

### Tools status

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
  * Stable
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

### Using HolBA in your HOL4-based project

To depend on HolBA in a project based on HOL4, we recommend setting up your project
to build using `Holmake`, and then adding references in your `Holmakefile` to
the directories where the modules from HolBA that you use reside in, relative to
the variable `HOLBADIR`.

For example, if you depend on modules in the `src/theory/bir` and
`src/theory/bir-support` directories, your `Holmakefile` may be as follows:

```make
INCLUDES = $(HOLBADIR)/src/theory/bir $(HOLBADIR)/src/theory/bir-support

all: $(DEFAULT_TARGETS)
.PHONY: all
```

To then build your project, you can export the path to your copy of the HolBA repository
and run `Holmake` in the directory with your `Holmakefile`, which will recursively
build all required theories:

```bash
export HOLBADIR=/path/to/holba
Holmake
```

## Related publications

- D. Lundberg, R. Guanciale, A. Lindner and M. Dam, **"Hoare-Style Logic for Unstructured Programs"**, in Software Engineering and Formal Methods, pp. 193-213, 2020. [Link](https://doi.org/10.1007/978-3-030-58768-0_11). _(program logic used for decomposition of verification)_
- H. Nemati, P. Buiras, A. Lindner, R. Guanciale and S. Jacobs, **"Validation of Abstract Side-Channel Models for Computer Architectures"**, in International Conference on Computer Aided Verification, pp. 225-248, 2020. [Link](https://doi.org/10.1007/978-3-030-53288-8_12). _(framework to validate abstract side-channel models)_
- A. Lindner, R. Guanciale and R. Metere, **"TrABin : Trustworthy analyses of binaries"**, Science of Computer Programming, vol. 174, pp. 72-89, 2019. [Link](https://doi.org/10.1016/j.scico.2019.01.001). _(the proof-producing binary analysis framework with weakest preconditions in HOL4)_
- D. Lundberg, **"Provably Sound and Secure Automatic Proving and Generation of Verification Conditions"**, Master Thesis, 2018. [Link](http://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Akth%3Adiva-239441).
- R. Metere, A. Lindner and R. Guanciale, **"Sound Transpilation from Binary to Machine-Independent Code"**, in 20th Brazilian Symposium on Formal Methods, pp. 197-214, 2017. [Link](https://doi.org/10.1007/978-3-319-70848-5_13). _(formalization of intermediate language and proof-producing lifter in HOL4)_
