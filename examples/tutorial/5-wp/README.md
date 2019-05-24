# Tutorial on Weakest Precondition Generation and Proving with HolBA

## Introduction

This directory contains a tutorial on how to obtain the weakest precondition of code segments, given their postconditions.

From the previous directory `4-bir-to-arm` we should have a number of contracts on code segments, in the shape of Hoare triples. The final goal is proving that these hold.

The current step consists of taking the postcondition and code segment of the contract, then generating and proving the corresponding _weakest precondition_, thereby obtaining a new Hoare triple. The weakest precondition is the least restrictive condition on the initial state so that it always leads to execution reaching a final state satisfying the postcondition. The theorems stating weakest preconditions corresponding with the individual BIR statements can be found in `bir_wpTheory`.

Since the postcondition and code segment are the same, proving the contract can be done (without going into details) by proving that the contractual precondition implies the weakest precondition. This will be performed in the next directory, `6-smt`.

## Stepwise walkthrough

Open `bir_wpScript.sml`. Start the HOL4 REPL, then open all the included theories and function libraries.

The main workhorse of this wtep will be `bir_obtain_ht`, a function which obtains a Hoare triple from the following arguments:

* `prog_tm`: The BIR program to analyse, in the form of a HOL term.
* `first_block_label_tm`: The label of the block where execution starts off (inclusive).
* `last_block_label_tm`: The label of the block where execution stops.
* `postcond_tm`: The Hoare triple postcondition stated as a BIR expression.
* `prefix`: A (preferably unique) prefix string which is used for naming all generated definitions.
* `false_label_l`: A list of labels, for which we will add dummy Hoare triples with `False` preconditions at the start of computation. This signifies blocks we do not want to jump to, and is used when conditional jumps are involved, where we instead want to generate separate HTs at conditional jumps.
* `defs`: A list of definitions containing the program definition, as well as all the definitions needed to rewrite the provided postcondition down to a pure BIR expression - this might contain some abbreviations.

In other words, you could say that you select the Hoare triple code segment from `prog_tm` using `first_block_label_tm` as the initial point and `last_block_label_tm` as the final point.

Now that we know what we need to call bir_obtain_ht, you can first assign the correct program term to `prog_tm` once and for all:

```
val prog_tm = (lhs o concl) bir_add_reg_prog_def;
```

Then we need to look at the contracts separately.

### `bir_add_reg_entry`

We define the string prefix like this:

```
val prefix = "add_reg_entry_";
```

Then we need to tell the function about the initial and final points of execution, which will give us the code segment we need from the program.

```
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
```

If you want, go back the the disassembly file and look at it to understand what the domain is of the current HT. Then we must assign a list of blocking dummy labels for `false_label_l`. However, this is just empty as long as execution does not land on a conditional jump:

```
val false_label_l = [];
```

We then assign as the postcondition the corresponding contract from `4-bir-to-arm`:

```
val postcond_tm = ``bir_add_reg_contract_1_post``;
```

And finally, we can supply `bir_obtain_ht` with some definitions. This always includes the program definition, and in addition to this it contains the definitions used to rewrite postcond_tm into a pure BIR expression.

```
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_1_post_def, bir_add_reg_I_def, BType_Bool_def];
```

## Technical details

TODO