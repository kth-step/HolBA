# "Concrete" execution with `add_reg`

## Experiments

1. See structure of `exec.sml`.
1. Run the script as it is.
1. Change inputs, run again and observe the outputs.
1. Change `n_max` with the control flow in mind, and observe:
  * intermediate register values,
  * flag values after the `cmp` instruction,
  * branching after the `b.gt` instruction.


## Execution and inspection

* Execute with `make` and read outputs in terminal window or `exec.log`.
* Relevant inputs are:
  * Stack pointer (`SP_EL0`)
  * Rarameter `x` (`R0`)
  * Parameter `y` (`R1`)
* Machine state contains the output variable `ly` (`R0`).
* Additionally, more registers and memory are used by the binary.
* Finally, processor flags like `ProcState_C` are assigned when computing the loop condition.

