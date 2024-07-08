# Smol BIR

This repository implements a fragment of the BIR language from [HolBA](https://github.com/kth-step/HolBA) using a evaluation relation in the theorem prover [HOL4](https://github.com/HOL-Theorem-Prover/HOL)


## Structure of the repository
The structure of this repository is as follows :
```
├─ examples : Examples on BIR usage
├─ src : source code of main theory
│   └─ theory : main BIR theories
│       ├─ bir_basicScript.sml : Basic Datatypes required of BIR expressions
│       ├─ bir_binexpScript.sml : Binary Expressions evaluation
│       ├─ bir_binpredScript.sml : Binary Predicate evaluation
│       ├─ bir_computeScript.sml : Computation function for BIR expressions
│       ├─ bir_envScript.sml : Variable Environment
│       ├─ bir_evalScript.sml : Evaluation relation for BIR expressions
│       └─ bir_unaryexpScript.sml : Unary Expressions evaluation
└─ test : Sanity checks theorems and tests
```


## Building
With a valid HOL4 `trindemossen-1` installation, you can run `Holmake` in the root directory of the repository.
