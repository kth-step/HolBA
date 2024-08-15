# Smol BIR

This repository implements a fragment of the BIR language from [HolBA](https://github.com/kth-step/HolBA) using a evaluation relation in the theorem prover [HOL4](https://github.com/HOL-Theorem-Prover/HOL)

## Overview of the repository's structure
The structure of this repository is as follows :
```
├─ examples/ : Examples on BIR usage
├─ src/ : source code of main theory
│   ├─ shared/ : useful libraries regarding BIR (mainly evaluation)
│   │   ├─ cv/ : Alternative BIR theory that can be used with cv_compute
│   │   ├─ bir_computeLib.{sml|sig} : Library to compute BIR terms
│   │   ├─ bir_cv_basicLib.{sml|sig} : Library to translate BIR terms to the cv equivalent theory
│   │   ├─ bir_cv_envLib.{sml|sig} : Library to translate BIR environments to the cv equivalent theory
│   │   └─ bir_cv_programLib.{sml|sig} : Library to translate BIR programs to the cv equivalent theory
│   └─ theory/ : main BIR theories
│       ├─ bir_basicScript.sml : Basic Datatypes required of BIR expressions
│       ├─ bir_binexpScript.sml : Binary Expressions evaluation
│       ├─ bir_binpredScript.sml : Binary Predicate evaluation
│       ├─ bir_computeScript.sml : Computation function for BIR expressions
│       ├─ bir_envScript.sml : Variable Environment
│       ├─ bir_evalScript.sml : Evaluation relation for BIR expressions
│       ├─ bir_ifthenelseScript.sml : If Then Else evaluation
│       ├─ bir_memScript.sml : Memory evaluation
│       ├─ bir_metaScript.sml : Proofs regarding BIR Meta-Theory
│       ├─ bir_typingScript.sml : Typing system for BIR expressions
│       └─ bir_unaryexpScript.sml : Unary Expressions evaluation
└─ test/ : Sanity checks theorems and tests
```

Additional `README`s are available in other key directories.


## Building
With a valid HOL4 `trindemossen-1` installation, you can run `Holmake` in the root directory of the repository.
Remark : Not all commits can be built as regular merge was used.
Tags are usually used to indicate “stable” release that can be built without errors

## Running the examples
Examples have an executable generated when you run `Holmake` in the root directory. 
You can run them either by running `Holmake test` in the directory or by executing the binary.
These executables act as benchmarks. The size of the input is hard-coded in the associated Lib file, usually by a parameter called `n` at the beginning of the `benchmark` function
