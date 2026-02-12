# `src/` directory

This directory contains the main script files for the BIR fragment.

## Eval vs Compute
Two equivalent definition of the BIR semantics are present in the files :
  - Computation-style or `compute` : This representation uses
  This representation is the one present in the original BIR from HolBA.
  It is more tailored toward doing computations.
  Definitions associated with this representation usually have `compute` in their name.
  - Relation-style or `eval` : This representation uses relations to define its semantics. 
  It is meant to be easier to understand for a new user, as inference rules are “easier” to understand. 
  Definitions associated with this representation usually have `eval` in their name.

These two uses the same datatypes.

## Key Files
Here are the key files of the directory :
  - `bir_basicScript.sml` : Most datatypes used by BIR.
  - `bir_envScript.sml` : Datatype for variable environment
  - `bir_metaScript.sml` : proofs regarding meta-theory (cf. below for more information regarding meta-theory)
  - `bir_computeScript.sml / bir_evalScript.sml` contain the general expression semantics of the two representation.
  - `bir_typingScript.sml` : Typing relation for BIR expressions. Useful for meta-theory
  - `bir_programSyntax.sml` : Statements and programs. Contains both an `eval` and `compute` definition of step
  - All other files contains semantics of the particular expression (ie. `bir_binexpScript.sml` contains semantics for Binary Expressions) for both `compute` and `eval`, as well as theorems about them.


## Meta-theory
The Meta-theory contains the theorems regarding expressions and programs.
Usually, the following theorems are proven :
  - `bir_eval_exp_correct_type` : When an expression evaluates to a value, the types are the same.
  - `well_typed_bir_eval_exp_value` : When an expression is correctly typed, then there exists some value to which the expression evaluates
  - `eval_eq_compute` : the `eval` and `compute` semantics are equivalent

## Compared to HolBA
The `compute` representation here is almost the same as the one in HolBA. Here are a few changes :
  - This representation doesn’t enforce type when using environment for variables.
  - In general, typing isn’t enforced by the semantics. This means that you can technically compute an `if then else` where the two bodies aren’t of the same type.
  All results in the meta-theory depends on typing.
  - Only a few operations are implemented. For example, Binary Expressions only support addition and bitwise AND
  - Memory cast (`BExp_Cast`) and Memory equality (`BExp_MemEq`) aren’t implemented
