# Tutorial on Weakest Precondition Generation and Proving with HolBA

## Introduction

This directory contains a tutorial on how to obtain the weakest precondition of code segments, given their postconditions.

From the previous directory `4-bir-to-arm` we should have a number of contracts on code segments, in the shape of Hoare triples. The final goal is proving that these hold.

The current step consists of taking the postcondition and code segment of the contract, then generating and proving the corresponding _weakest precondition_, thereby obtaining a new Hoare triple. The weakest precondition is the least restrictive condition on the initial state so that it always leads to execution reaching a final state satisfying the postcondition. The theorems stating generic weakest preconditions corresponding with the individual BIR statements can be found in `bir_wpTheory`.

Since the postcondition and code segment are the same, proving the contract can be done (without going into details) by proving that the contractual precondition implies the weakest precondition. This will be performed in the next directory, `6-smt`.

## Stepwise walkthrough

Open `bir_wpScript.sml`. Start the HOL4 REPL, then open all the included theories and function libraries.

The main workhorse of this step will be `bir_obtain_ht`, a function which obtains a Hoare triple from the following arguments:

* `prog_tm`: The BIR program to analyse, in the form of a HOL term.
* `first_block_label_tm`: The label of the block where execution starts off (inclusive).
* `last_block_label_tm`: The label of the block where execution stops.
* `postcond_tm`: The Hoare triple postcondition stated as a BIR expression.
* `prefix`: A (preferably unique) prefix string which is used for naming all generated definitions.
* `false_label_l`: A list of labels, for which we will add dummy Hoare triples with `False` preconditions at the start of computation. This signifies blocks we do not want to jump to, and is used when conditional jumps are involved, where we instead want to generate separate HTs at conditional jumps.
* `defs`: A list of definitions containing the program definition, as well as all the definitions needed to rewrite the provided postcondition down to a pure BIR expression - this might contain some abbreviations.

In other words, you could say that you select the Hoare triple code segment from `prog_tm` using `first_block_label_tm` as the initial point and `last_block_label_tm` as the final point.

Now that we know what we need to call `bir_obtain_ht`, you can first assign the correct program term to `prog_tm` once and for all:

```sml
val prog_tm = (lhs o concl) bir_add_reg_prog_def;
```

Note that the term just contains `bir_add_reg_prog`, which is an abbreviation of the program. This means that the definition of `bir_add_reg_prog` must be used to evaluate the program. Since term matching is much more efficient using abbreviations. 

Then we need to look at the contracts separately.

### `bir_add_reg_entry`

The string prefix is used inside `bir_obtain_ht` to define uniquely named terms, as well as assigning these definitions to uniquely named SML values.
We choose a name which will identify theorems and definitions with the entry contract:

```sml
val prefix = "add_reg_entry_";
```

Then we need to tell the function about the initial and final points of execution, which will give us the code segment we need from the program. If you want, go back the the disassembly file in `1-code` and look at it to understand what the domain of the current HT is.

Note that in general, the HT execution could end when any label out of a set of labels is reached. For example, this would be the case for code which branches out to multiple exit points. Sets of ending labels are supported by the current WP generation and proving procedure, however different postconditions for different end labels are not.

For this exercise we will only treat single last block labels.

```sml
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
```

`false_label_l` is a list of block labels for which we assign dummy HTs with False as precondition.

This can be hard to understand intuitively. First, consider a HT with False as precondition. Since an antecedent of the HT would be that False holds, any conclusion would always hold. This is stated by the theorem `bir_exec_to_labels_pre_F` in `bir_wpTheory`. Since this is universally true, we are always free to assume such a HT.

Since HTs are generated incrementally from the end of execution to the start, when a block which could jump to a block with dummy HT is processed, the resulting HT would in effect be stating the effect of execution assuming we do not jump to the block with a dummy HT.

Concretely, this mechanism is used in cases with conditional jumps, where one of the jump targets signifies loop continuation. It allows us to separately generate HTs for loop continuation and loop exit, which we then can compose.

For the `bir_add_reg_entry` contract, `false_label_l` is just an empty list:

```sml
val false_label_l = [];
```

We then assign as the postcondition the corresponding contract from `4-bir-to-arm`.

Note that just like `prog_tm`, this holds just an abbreviation, so we also need the definitions needed to see the concrete BIR expression.

```sml
val postcond_tm = ``bir_add_reg_contract_1_post``;
```

And finally, we can supply `bir_obtain_ht` with a list of definitions. This list must contain all definitions needed to fully expand the program (`prog_tm`) and the postcondition (`postcondition_tm`) into their explicit forms, using only regular BIR syntax from `theory/bir`. Please open the definitions to see what we are dealing with.

```sml
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_1_post_def, bir_add_reg_I_def, BType_Bool_def];
```

You might ask why `prog_tm` and `postcond_tm` do not contain the explicit values, and why the definition list is needed. In fact, calling `bir_obtain_ht` like this would also work. However, never abbreviating commonly used terms would make proofs much slower, since we would be forced to match entire explicit abbreviations at every point, instead of abbreviations (for example with `MATCH_MP`).

On the other hand, if you only ever wanted to use definitions with abbreviations, the `prog_tm` and `postcond_tm` terms are not needed as arguments, since these can be obtained from the definitions. The current approach has chosen flexibility over optimization.

There is also the vague urge of avoiding to generate definitions automatically. Possibly it is good programming practice to make it very explicit to the use where definitions are introduced.

Next, we call `bir_obtain_ht`:

```sml
val (bir_add_reg_entry_ht, bir_add_reg_entry_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
```

`bir_obtain_ht` is a convenient wrapper function created for this tutorial, which internally uses functions from `bir_wpLib`. The return value is a tuple, which firstly contains a theorem stating the HT with the following components:

* __Precondition__: The _weakest precondition_, obtained from the postcondition and executed code segment through the WP predicate transformer semantics
* __Execution__: From `first_block_label_tm` to `last_block_label_tm`, never branching to `false_label_l`
* __Postcondition__: `postcond_tm` (the contractual postcondition)

and secondly, simply the weakest precondition as a term. In order to be able to export the results to a compiled theory, we then define an abbreviation for the WP and save the theorem stating the HT:

```sml
val bir_add_reg_entry_wp_def =
  Define `bir_add_reg_entry_wp = ^(bir_add_reg_entry_wp_tm)`;
val _ = save_thm ("bir_add_reg_entry_ht", bir_add_reg_entry_ht);
```

### `bir_add_reg_loop`

This is the code segment containing the loop body - `0x20` to `0x40`.

Obtaining this HT is rather analoguous to the one above, so no further explanation is needed. You might want to look at the disassembly again to see which code segment is currently being treated.

### `bir_add_reg_loop_continue`

This is the code segment describing loop continuation. HT execution starts at the conditional jump at the endpoint of the loop (`0x40`), then branches back to the loop start (`0x20`). This is ensured by `false_label_l`, which now contains the other target of the conditional jump:

```sml
val false_label_l = [``BL_Address (Imm64 0x44w)``];
```

Adding a dummy HT with False as precondition for this address ensures that the HT obtained for `bir_add_reg_loop_continue` only describes the scenario where the loop continues.

### `bir_add_reg_loop_exit`

The HT generated here covers the case opposite to the previous HT. We start at the endpoint of the loop (`0x40`), exit the loop (to `0x44`), and use `false_label_l` to forbid loop continuation:

```sml
val false_label_l = [``BL_Address (Imm64 0x44w)``];
```

### `bir_add_reg_loop_variant`

This part is similar to `bir_add_reg_loop`. The difference lies in the postcondition, which now features a free variable. This free variable is used to state that the loop variant is strictly decreasing with every loop iteration.

Other than the different contract, there is not much to say about this part. However, inside `bir_obtain_ht`, the free variable must be taken special care of in several places.

### `bir_add_reg_loop_continue_variant`

Just like the above, but similar instead to `add_reg_loop_continue`. 

### Bonus: `bir_add_reg_mem`

What about the preamble of the function, where the arguments are loaded from the stack into registers? And the final instruction, where the stack pointer is reset?

This should also be verified, however it is not currently a part of verification due to issues with memory simplification which bungle the step involving the SMT solver.

This part - with execution from `0x0` to `0x1c` shows that we can still generate WPs for this situation. Observing these should help illustrate the importance of simplification of memory access.

## Technical details

Open `../support/tutorial_wpSupportScript.sml`. In this file, `bir_obtain_ht` is defined. The arguments should have identical names to the values assigned to in `tutorial_wpScript.sml`, so you are free to start executing things inside the function as soon as you have opened the included theories and libraries and the other functions in the file.

Most of the interesting functions used inside `tutorial_wpSupportScript.sml` can be found in `../../../src/tools/wp/bir_wpLib.sml`. You can continue walking through these if you just make the commented-out assignments in `bir_obtain_ht` before, to make sure the values match the function arguments.