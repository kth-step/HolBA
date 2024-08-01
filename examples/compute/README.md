# Smol BIR

This repository implements a fragment of the BIR language from [HolBA](https://github.com/kth-step/HolBA) using a evaluation relation in the theorem prover [HOL4](https://github.com/HOL-Theorem-Prover/HOL)


## Structure of the repository
The structure of this repository is as follows :
```
├─ examples/ : Examples on BIR usage
├─ src/ : source code of main theory
│   ├─ shared/ : useful libraries regarding BIR (mainly evaluation)
│   │   ├─ cv/ : Alternative BIR theory that can be used with cv_compute
│   │   ├─ bir_computeLib.{sml|sig} : Library to compute BIR terms
│   │   ├─ bir_cv_basicLib.{sml|sig} : Library to translate BIR terms to the cv equivalent theory
│   │   └─ bir_cv_envLib.{sml|sig} : Library to translate BIR environments to the cv equivalent theory
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


## Building
With a valid HOL4 `trindemossen-1` installation, you can run `Holmake` in the root directory of the repository.
