# SCAM-V
This is the SCAM-V (Validation of Abstract Side-Channel Models for Computer Architectures) tool for HolBA.


## Entry point and command line arguments
The entry point for SCAM-V is the function `scamv_run` in `bir_scamv_driverLib.sml`.
When this function is called, it generates the test cases for an experiment set according to a configuration and terminates.
It takes several arguments as one structured record representing the configuration for a whole test case generation run.
The possible options range from sizes for the desired experiment set, over generation options like program types and observation models, to miscellaneous like output verbosity and random number generator seeding.
The simple interface function `scamv_run_with_opts` of the same library may be used to create a configuration structure from command line arguments and initiate a SCAM-V run.
This function uses the infrastructure from `scamv_configLib.sml` to parse the command line arguments from the environment.

Currently, a user of SCAM-V may simply run the script `examples/scamv.sh` from the command line with appropriate arguments.
There is the even more convenient option of using the SCAM-V process scripts in `examples/scripts`, which also provide support for parallelizing the test case generation and experiment running on real hardware.
These scripts introduce configuration files in `examples/expgenruns`.
See the documentation in [examples](https://github.com/kth-step/HolBA/tree/dev_scamv/src/tools/scamv/examples) for understanding these scripts and the process around this.


## Components
The main components of SCAM-V are the various program generators and observation models as well as the core process of SCAM-V together with its libraries.
See the following sections for more details on the program generators and observation models.

The components of SCAM-V are:
- Program generators - `bir_prog_genLib`, `bir_gccLib`
  - Random generators
    - ARMv8 ISA syntax based - `bir_prog_gen_randLib` (`regExLib`)
    - ARMv8 program slicing - `bir_prog_gen_sliceLib`
  - Monadic generators
    - Quickcheck - `qc_genLib`
    - ARMv8 generator collection - `asm_genLib`
    - ARMv8 generator "prefetch" - `armv8_prefetch_genLib`
- Observation modelling
  - ARMv8 observation model collection - `bir_obs_modelTheory`, `bir_obs_modelLib`
- SCAM-V main process chain and core libraries
  - SCAM-V driver - `bir_scamv_driverLib`
  - Symbolic execution engine - directory `symbexec`, `bir_conc_execLib`
  - Relation synthesis - `bir_rel_synthLib`
- Misc
  - SCAM-V shell scripts - directory `examples`
  - Configuration parser - `scamv_configLib`
  - Experiment storage and execution - `bir_embexp_driverLib`
  - Helper functions - `bir_scamv_helpersLib`


## Program generators
The program generators in SCAM-V can be divided into random generators with less configurable structure and the more structured monadic generators.
A semi-uniform interface for each generator is provided in the library `bir_prog_genLib`.
This includes a consistency check using a trial-assembly-approach of the generated programs to make the SCAM-V chain more resilient.

For random program generation, we currently support a random instruction sequence generation and a program slicing generator.
The sequence generator uses the instruction syntax provided from the ARMv8 model and randomly generates the operators like register names.
It applies a hard-coded weight-function to the possible instruction to bias generation.
The slice generator takes a binary and returns randomly sliced out sections from this binary.

For structured monadic program generation, we provide a quickcheck library to support further development of quickcheck-style generators.
This library enables succint representations of intended program structures, which is used in a collection of generators as well as a generator to trigger the ARMv8 prefetching with load stride patterns.
The collection consists of a simple load generator as well as a family of generators to trigger "previction".

New program generators can be added as follows:
1. Add a library or a functions to the existing libraries.
1. Add an interface function in the general library.
1. Add a configuration option to the SCAM-V configuration parser.
1. Add a new case to handle the new option in the SCAM-V driver.
The commit history of this directory should be useful to understand how previous additions have been made.


## Observation models
All our observation models are currently in one library and and accompanying theory.
The theory contains HOL4 definitions to describe the code augmentation with observations as well as memory location constraints according to the experiment setup.
The library is simply an interface that applies the definitions to obtain a program with observations accordingly.

We have the following observation models to be used for the Raspberry Pi 3 (ARMv8) cache geometry:
- Cache tag and set index
- Cache tag only
- Cache set index only
- Cache tag and set index for a partition of the cache (not aligned to page boundary)
- Cache tag and set index for a partition of the cache (aligned to page boundary)

New observation models can be added as follows:
1. Add a HOL4 function to transform a program to add observations.
1. Add an SML library function to use the new HOL4 definition.
1. Add a configuration option to the SCAM-V configuration parser.
1. Add a new case to handle the new option in the SCAM-V driver.
The commit history of this directory should be useful to understand how previous additions have been made.

