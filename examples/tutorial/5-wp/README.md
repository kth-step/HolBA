# 5 Generating and Proving Weakest Preconditions

## Introduction

This directory contains a tutorial on how to obtain the _weakest precondition_ of BIR code segments, given their postconditions. The weakest precondition is the least restrictive condition on the initial state so that it always leads to execution reaching a final state satisfying the postcondition. The theorems stating generic weakest preconditions corresponding with the individual BIR statements can be found in `bir_wpTheory`.

From the previous directory `4-bir-to-arm` we should have a number of to-be-proven contracts on code segments, in the shape of Hoare triples. The goal here is obtaining the weakest preconditions of their postconditions, after which they we will prove in the next step (`6-smt`) that these weakest preconditions imply the contractual preconditions, from which we obtain the to-be-proven Hoare triples.

## Stepwise walkthrough

Open `tutorial_wpScript.sml`. Start the HOL4 REPL, then open all the included theories and function libraries.

The main workhorse of this step will be `bir_obtain_ht`, a function which obtains a Hoare triple from the following arguments:

prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

* `prog_tm`: The BIR program to analyse, in the form of a HOL term.
* `first_block_label_tm`: The label of the block where execution starts off (inclusive).
* `ending_set`: A set of labels for which execution ends and the postcondition must hold. Note that the set of labels must not be a HOL4 set, but can be any function with the type signature `bir_label_t -> bool`.
** `ending_set_to_sml_list`: A SML function which takes a term representing a set and obtains an SML list of labels in the program which are contained in the set.
* `postcond_tm`: The Hoare triple postcondition stated as a map from labels to BIR expressions.
** `postcond_exp_from_label`: A SML function taking a label term and obtaining a BIR expression term with the postcondition for the given label.
* `prefix`: A (preferably unique) prefix string which is used for naming all internally generated definitions.
* `defs`: A list of definitions containing the program definition, as well as all the definitions needed to rewrite the provided pre-and postconditions down to a BIR expression - typically some abbreviations.

In other words, you could say that you select the Hoare triple code segment from `prog_tm` using `first_block_label_tm` as the initial point and `ending_set` as the final points.

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

Then we need to tell the function about the initial and final points of execution, which will give us the code segment we need from the program. If you want, go back the the disassembly file in `1-code` and look at it to understand what the domain of the current HT is. This code segment starts before the loop and goes all the way to the branch point.

Additionally, we add `0x48` as an ending point (even though this will never be reached before `0x40`) in order to compose with Hoare triples ending at `0x48` later on.

```sml
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``;
val ending_set =  ``{BL_Address (Imm64 0x40w); BL_Address (Imm64 0x48w)}``;
```

Since this ending label set is a regular good old HOL4 set, we can use `strip_set` from `pred_setSyntax` to obtain an SML list of labels from it. This is mapped to `ending_set_to_sml_list` in `bir_wp_interfaceLib`.

We then assign as the postcondition the corresponding contract from `4-bir-to-arm`.

```sml
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x40w))
                        then bir_add_reg_contract_1_post
                        else bir_exp_false``;
```

Note that this maps all labels apart from `0x40` onto `bir_exp_false`, meaning the the contract will ensure those are not reached. In other words, you could say they are blacklisted. Specifically, this is done for `0x48`.

Just like `prog_tm`, this otherwise holds just an abbreviation for the postcondition, so we also need the definitions needed to see the concrete BIR expression. As for the function needed to obtain a BIR expression from the above, this is also given in `bir_wp_interfaceLib`:

```sml
fun postcond_exp_from_label postcond label =
  (snd o dest_eq o concl)
    (SIMP_CONV
      (bool_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss) []
      (mk_comb (postcond, label)
    )
  )
;
```

And finally, we also supply `bir_obtain_ht` with a list of definitions. This list must contain all definitions needed to fully expand the program (`prog_tm`) and the postcondition (`postcondition_tm`) into their explicit forms, using only regular BIR syntax from `theory/bir`. Please open the definitions (e.g. `bir_add_reg_contract_1_post_def;`, <kbd>↵ Enter</kbd> in the HOL4 REPL) to see what we are dealing with.

```sml
val defs = [bir_add_reg_prog_def,
            bir_add_reg_contract_1_post_def,
            bir_add_reg_I_def,
            bir_exp_false_def,
            BType_Bool_def];
```

You might ask why `prog_tm` and `postcond_tm` do not contain the explicit values, and why the definition list is needed. In fact, calling `bir_obtain_ht` like this would also work. However, never abbreviating commonly used terms would make proofs much slower, since we would be forced to match entire explicit abbreviations at every point, instead of abbreviations (for example with `MATCH_MP`).

On the other hand, if you only ever wanted to use definitions with abbreviations, the `prog_tm` and `postcond_tm` terms are not needed as arguments, since these can be obtained from the definitions. The current approach has chosen flexibility over performance optimization.

There is also the vague urge of avoiding generation of definitions automatically. Possibly it is good programming practice to make it very explicit where definitions are introduced.

Next, we call `bir_obtain_ht`:

```sml
val (bir_add_reg_entry_ht, bir_add_reg_entry_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;
```

`bir_obtain_ht` is a convenient wrapper function created for this tutorial, which internally uses functions from `bir_wpLib`. The return value is a tuple, which firstly contains a theorem stating the HT with the following components:

* __Precondition__: The _weakest precondition_, obtained from the postcondition and executed code segment through the WP predicate transformer semantics
* __Execution__: From `first_block_label_tm` to `ending_set`
* __Postcondition__: `postcond_tm` (the contractual postcondition)

and secondly, simply the weakest precondition as a term. In order to be able to export the results to a compiled theory, we then define an abbreviation for the WP and save the theorem stating the HT:

```sml
val bir_add_reg_entry_wp_def =
  Define `bir_add_reg_entry_wp = ^(bir_add_reg_entry_wp_tm)`;
val _ = save_thm ("bir_add_reg_entry_ht", bir_add_reg_entry_ht);
```

### `bir_add_reg_loop_variant`

This is the code segment containing the loop body - `0x20` to `0x40`. Similar to previously, we also have `0x48w` in the ending set, but now for two reasons. Firstly, we want to avoid branching out of the loop. Secondly, we want to compose later on with the post-loop content, which has this as end point. Accordingly, the postcondition now is

```sml
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x40w))
                        then bir_add_reg_contract_2_post_variant v
                        else bir_exp_false``;
```

which is similar to previously, apart from the addition of `v` as just a free variable inside the postcondition expression. This is used internally in the expression to denote the value of the loop variant at the beginning of the loop.

Obtaining this HT is rather analoguous to the one above in the other respects, so no further explanation is needed. You might want to look at the disassembly again to see which code segment is currently being treated.

### `bir_add_reg_loop_continue_variant`

This is the code segment describing loop continuation. HT execution starts at the branch point of the loop (`0x40`), then branches back to the loop start (`0x20`). This is ensured by the ending set and the postcondition:

```sml
val ending_set = ``{BL_Address (Imm64 0x20w); BL_Address (Imm64 0x40w); BL_Address (Imm64 0x48w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x20w))
                        then bir_add_reg_contract_3_post_variant v
                        else bir_exp_false``;
```

We can't reach `0x20` again - this is a property needed when composing the loop. We want the postcondition to hold at the branch-back point `0x20` and we don't want `0x48` to be reached, which is needed when composing with post-loop code.

### `bir_add_reg_loop_exit`

The HT generated here covers the case opposite to the previous HT. We start at the branchpoint of the loop (`0x40`), then exit the loop and reach the end of the program (at `0x48`), and use the ending set and postcondition to forbid loop continuation:

```sml
val ending_set = ``{BL_Address (Imm64 0x20w); BL_Address (Imm64 0x48w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x48w))
                        then bir_add_reg_contract_4_post
                        else bir_exp_false``;
```

### Bonus: `bir_add_reg_mem`

What about the preamble of the function, where the arguments are loaded from the stack into registers? And the final instruction, where the stack pointer is reset?

This should also be verified, however it is not currently a part of verification due to issues with memory simplification which bungle the step involving the SMT solver.

This part - with execution from `0x0` to `0x1c` shows that we can still generate WPs for this situation. Observing these should help illustrate the importance of simplification of memory access.

## Technical details

Open `../support/tutorial_wpSupportScript.sml`. In this file, `bir_obtain_ht` is defined. The arguments should have identical names to the values assigned to in `tutorial_wpScript.sml`, so you are free to start executing things inside the function as soon as you have opened the included theories and libraries and the other functions in the file.

Most of the interesting functions used inside `tutorial_wpSupportScript.sml` can be found in `../../../src/tools/wp/bir_wpLib.sml`. You can continue walking through these if you just make the commented-out assignments in `bir_obtain_ht` before, to make sure the values match the function arguments.