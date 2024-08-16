# `shared/` directory

This directory contains libraries related to computation using the `cv` library

## Key files
Here are the key files of the directory :
  - `cv/` : Alternative definition of BIR more suitable for `cv` computation. 
  Usually, definitions related to that representation are prefixed by `bir_cv`
  The key differences between are given below. 
    - `cv/bir_cv_computeScript.sml` also contains the equivalence proof between the two representations
  - `bir_computeLib.sml` : Library to compute expressions and step through programs. 
  This is the file that should be imported when you want to do evaluations.
  An overview of the usage is given below
  - `bir_cv_*Lib.sml` : Libraries containing conversions (as in HOL4's `conv`) from the original BIR datatypes to the BIR CV datatypes.
  This library is used extensively by `bir_computeLib.sml` and is not necessary to use outside of it.


## Differences between representations
Here are the most important differences between the original BIR (in `theory/`) and the `bir_cv` representation :
| Datatype | BIR | CV |
| ------------- | -------------- | -------------- |
| Environment | Function `ident -> val option` | Association List `ident # val` |
| Memory maps | Finite map `num \|-> num` | Association List `num # num` |
| Program Counter / State / Block | Records | Tuples |

Some functions were also slightly changed to be easier to use with `cv`, like removing a higher-order parameter and hard-coding it or using an auxiliary function instead of a function from the list library.


## Usage of `bir_computeLib`
To use `bir_computeLib` in a file where you want to evaluate expressions or step through programs :
  - You should first load the library using `open bir_computeLib`. 
  This will automatically do the translation using `cv_trans` of the computation functions so this might take a while.
  - You can either use the `EVAL` variants like `compute_exp_EVAL` if you want to use `EVAL` or,
  - You can use the `cv_compute` library :
    - Create definition of the term you want to evaluate, usually using `Definition`
    - Use a translation function like `translate_exp_cv` to prepare the evaluation (it uses `cv_trans_deep_embedding`). This is a one time cost
    - You can now use a `compute_*_cv` function like `translate_exp_cv` and feed it the definition of the term.
  
