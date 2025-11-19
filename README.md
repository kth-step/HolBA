# HolBA-SE

This README describes the artifact for the VMCAI 2026 paper 
"Forward Symbolic Execution for Trustworthy Automation
of Binary Code Verification". We refer to the artifact as HolBA-SE.

## Artifact overview

HolBA-SE is an extension of the HolBA library for binary analysis
(https://github.com/kth-step/holba). In turn, HolBA depends on the
HOL4 theorem prover, implemented in Standard ML (SML). HolBA-SE
relies specifically on the Poly/ML compiler.

HolBA-SE directories are as follows:

- `scripts`: installation scripts
- `src`: SML sources for HolBA-SE library
- `examples/riscv`: SML sources for RISC-V application
- `examples/arm_cm0`: SML sources for ARM Cortex-M0 application
- `src_exectime`: sources for the ARM Cortex-M0 benchmark binary,
   the hardware testing harness, and the AbsInt aiT project files
- `logs`: contains the various logs for our verification applications,
   and also from hardware testing and AbsInt aiT runs

Notable subdirectories:

- `src/theory/tools/symbexec`: HOL4 symbolic execution theory, BIR instantiation
- `src/tools/symbexec`: SML functions for applying symbolic execution results
- `examples/riscv/chacha20`: ChaCha20 cipher case study
- `examples/riscv/kernel-trap`: RISC-V kernel case study

We estimate the artifact takes around two hours to build and replicate
on a modern machine. We tested on an Intel Core i5-9600K with 32GB RAM.
Less RAM than 32GB is unlikely to work, due to demanding case studies.

## Getting Started Guide

### Alternative 1: using bundled Dockerfile

We provide a Dockerfile in the artifact root directory
(where this README resides) that can be used to bootstrap
and enter an environment for replicating results:

```shell
$ docker build -t holbase .
$ docker run -it --rm holbase
```

This requires an x86 environment and takes 20-25 minutes on a modern machine.
The second docker command enters the shell where the step-by-step instructions
below can be run.

### Alternative 2: manual installation of dependencies

HolBA-SE can be replicated outside Docker by manually installing
the following dependencies:

- Poly/ML, version 5.7.1 or later (https://github.com/polyml/polyml/releases)
- HOL4, tag trindemossen-1 (https://github.com/HOL-Theorem-Prover/HOL/releases/tag/trindemossen-1)
- Z3, version 4.14.1 (https://github.com/Z3Prover/z3/releases/tag/z3-4.14.1)

HolBA is then built using the `Holmake` tool bundled with HOL4. To let HolBA
know where to find the `z3` binary, its path must be set via the environment:

```shell
$ export HOL4_Z3_EXECUTABLE=/path/to/bin/z3
```

Assuming Holmake is in the path, this should give an environment equivalent
to the Docker one in this shell.

## Step-by-Step Instructions for Replication

### 0. Building HolBA-SE

In the root directory (where this README resides), run:

```shell
$ Holmake
```

This takes 10-20 minutes on a modern machine.

The result should be output with lots of "OK".

### 1. HOL4 definitions and theorems

Machine-checked definitions and theorems in HOL4 have the SML type `thm`.
All of these definitions and theorems are checked in the previous step,
but they can be inspected for reassurance. This is easiest done by
starting a HOL4 toplevel from the root directory:

```shell
$ hol --holstate src/holba-heap
```

This will give a prompt starting with ">" that can be exited with Ctrl+d.

Using the prompt, Definition 1 can be inspected as follows:
```
> symb_recordTheory.symb_matchstate_def;
```

Theorem 1:
```
> bir_symb_soundTheory.birs_symb_step_sound_thm;
```

Definition 2:
```
> symb_recordTheory.symb_minimal_interpretation_def;
```

Definition 3:
```
> symb_recordTheory.symb_matchstate_ext_def;
```

Definition 4:
```
> symb_recordTheory.symb_hl_step_in_L_sound_def;
```

Theorem 2: 
```
> symb_prop_transferTheory.symb_prop_transfer_thm;
```

Figure 3, rule symbstep:
```
> symb_rulesTheory.symb_rule_STEP_thm;
```

Figure 3, rule case:
```
> symb_rulesTheory.symb_rule_SPLIT_thm;
```

Figure 3, rule infeasible:
```
> symb_rulesTheory.symb_rule_INF_thm;
```

Figure 3, rule rename:
```
> symb_rulesTheory.symb_rule_SRENAME_thm;
```

Figure 3, rule freesymb_rename:
```
> symb_rulesTheory.symb_rule_SRENAME_FREE_thm;
```

Figure 3, rule subst:
```
> symb_rulesTheory.symb_rule_INST_thm;
```

Figure 4, rule simplify:
```
> symb_rulesTheory.symb_rule_FRESH_thm;
```

Figure 4, rule consequence:
```
> symb_rulesTheory.symb_rule_CONS_thm;
```

Figure 4, rule transfer:
```
> symb_rulesTheory.symb_rule_STRENGTHEN_thm;
```

Figure 4, rule sequence:
```
> symb_rulesTheory.symb_rule_SEQ_thm;
```

### 2. Evaluation of symbolic execution (Table 1)

Starting from the root directory, run:
```shell
$ cd examples/riscv && ./collect_experiment_data.py
```

This takes 5-10 minutes on a modern machine.

The final output should have symbolic execution time in seconds
for all example programs in Table 1. This data is also stored
in the file experiment_data.log. We provide a local sample of
experiment_data.log in logs/riscv/experiment_data.log for
comparison.

### 3. RISC-V functional verification case studies (Section 6)

To check the ChaCha20 cipher case study, start from the root directory and run:
```shell
$ cd examples/riscv/chacha20 && Holmake
```

This can take 5-10 minutes on a modern machine.

The output should include a bunch of "OK".

Key files that are checked:
- `examples/riscv/chacha20/chachaScript.sml` - abstract definition of ChaCha
- `examples/riscv/chacha20/chacha20_spec_riscvScript.sml` - ChaCha20 column round and diagonal round pre/postconditions
- `examples/riscv/chacha20/chacha20_column_round_propScript.sml` - ChaCha20 column round RISC-V contract theorem (see near end of file)
- `examples/riscv/chacha20/chacha20_diagonal_round_propScript.sml` - ChaCha20 diagonal round RISC-V contract theorem (see near end of file)
- `examples/riscv/chacha20/chacha_equivScript.sml` - theorems showing equivalence between abstract ChaCha definitions and definitions used in RISC-V contracts

To check RISC-V kernel case study, start from the root directory and run:

```shell
$ cd examples/riscv/kernel-trap && Holmake
```

This can take 5-10 minutes on a modern machine.

The output should include a bunch of "OK".

Key files that are checked:
- `examples/riscv/kernel-trap/kernel_trap_spec_riscvScript.sml` - RISC-V pre/postconditions
- `examples/riscv/kernel-trap/kernel_trap_entry_propScript.sml` - trap_entry RISC-V contract (see near end of file)
- `examples/riscv/kernel-trap/kernel_trap_return_propScript.sml` - trap_return RISC-V contract theorem (see near end of file)

### 4. Cortex-M0 execution time verification case studies (Section 7)

Checking the execution time evaluations in Section 7 consists of two parts.

#### Reproducing verification results

To check the verification results using HolBA-SE, start from the root directory and run:
```shell
$ ./src_exectime/holba-se_run_all.sh
```

This takes about an hour on a modern machine.

The output should include a bunch of "OK".

Key files that are checked:

- `examples/arm_cm0/tiny/tiny_analysisScript.sml` - ldldbr8 example
- `examples/arm_cm0/aes/aes_o0_wholeScript.sml` - aes example
- `examples/arm_cm0/aes/aes_o0_loopScript`.sml - subfragment for aes example (loop body)
- `examples/arm_cm0/modexp_simple/modexp_asm_uidivmodScript.sml` - subfunction for modexp example
- `examples/arm_cm0/modexp_simple/modexp_asmScript.sml` - modexp example
- `examples/arm_cm0/motor_set/motor_o0Script.sml` - motor_set example
- `examples/arm_cm0/motor_set/motor_o3Script.sml` - motor_set example at optimization level o3
- `examples/arm_cm0/balrob/v2-faster/*Script.sml` - a set of subfunctions for pid example
- `examples/arm_cm0/balrob/v2-faster/balrob_topScript.sml` - pid example

The outputs of the verification tool reside in the various `.hollogs`
directories and are automatically copied into the `logs/armcm0/holba-se`
directory with simpler names. These files contain the evaluation times,
the validated execution times, and manually exctracted execution times
for return instructions.

For easier search of the result values, the `logs/armcm0/holba-se` directory
is preloaded with logs from one of our runs, where irrelevant information
has been removed.

Note that the validated execution times have to be added together with the
return times as they are not accounted for as symbolic execution stops
before executing the return instructions. This is done so that the values
in the table are as comparable as possible (testing and holba-se use the
same counting, while aiT starts from an empty pipeline and also includes
return instructions).

For example, after a successful run, the file `logs/armcm0/holba-se/aes`
will contain the following:
```
!!! RESULT !!!
[oracles: BIRS_CONST_LOAD, BIRS_CONTR_Z3, BIRS_IMP_Z3,
 BIRS_PCOND_SAT_Z3, BIRS_SIMP_Z3, DISK_THM]
[axioms: ]

BExp_IntervalPred (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
  (BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 3755w)),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 3755w)))
cycles for returning from this function at 0x8009558w (pop {r7, pc}) are: 6
```

Adding 6 cycles to 3755, we get 3761 as the best and worst cycle count,
which is the constant time for aes presented in Table 2. Also, at the end
of `logs/armcm0/holba-se/aes`, there is the HOL4 evaluation time, which will
be similar to the following:
``` 
Exporting theory "aes_o0_whole" ... done.
Theory "aes_o0_whole" took 8m32s to build
```

However, the exact evaluation time will vary. For example, some subfunctions
of the pid example run in parallel, while other subfunctions or subfragments
run in sequence. This has to be taken into account when determining the overall
times for symbolic execution.

#### Data from AbsInt aiT tool

Reproducing the "aiT" column of Table 2 requires the proprietary aiT
tool (https://www.absint.com/ait/index.htm) and an appropriate license.
The aiT project files for this reside in `src_exectime/aiT`. In case this
is not available, the `logs/armcm0/aiT` directory contains our collected
outputs. They are the same for the same binary even if the tool runs
multiple times.

Regarding the sentence with "two subsequent calls to motor_set o3" in
Section 7.2, the counterexample is already shown with function itself.
The argument is that aiT counts 2-3 more cycles due to their processor model,
which assumes an empty pipeline at start. Our counting instead is like the
one given in the ARM Cortex-M0 reference manual, which means that aiT WCET
values are at least two cycles higher than ours (both testing and HolBA-SE
upper execution time bounds). By this argument, aiT WCET values that are
strictly smaller than the highest measured value plus 2 constitute counterexamples
to WCET soundness. For the motor_set o3 example we also include a symbolic
execution without overapproximation (the corresponding theorem includes AIO
in the name and is produced in the same log file) and this confirms the highest
observed execution time during testing (i.e., 91 cycles) is indeed the lowest
upper execution time bound. The same argument about counterexamples applies to
the WCET value of aiT for the aes example, for which all values in the table
are identical.

#### Data from testing on hardware

Reproducing the "testing" column of Table 2 requires a specialized
hardware setup, which is described in the EmbExp-Box repository
(https://github.com/kth-step/embexp-box), which is also required
for data collection. Given those in place, log collection is executed
by the testing harness in src_exectime/testing, which is executed with
the script run_all_testing.sh. We collected and included three sets
of hardware testing logs in `logs/armcm0/testing.
