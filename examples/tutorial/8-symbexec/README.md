# Symbolic execution with `add_reg`

## Experiments

1. See structure of `exec.sml`.
1. Run the script as it is.
1. Change initial path condition, and observe:
  * the path conditions (see contradictions for infeasible paths),
  * number of resulting symbolic states (leafs in execution tree).
1. Change `maxdepth` with the control flow in mind, and observe the number of leafs.
1. Think: A proof-producing implementation would allow
  * verification by transforming the produced paths into the strongest postcondition,
  * computing worst-case execution times, and
  * more :).


## Execution and inspection

* Execute with `make` and read outputs in terminal window.
* Relevant inputs for the path condition:
  * Stack pointer (`SP_EL0`)
  * Rarameter `x` (`R0`)

