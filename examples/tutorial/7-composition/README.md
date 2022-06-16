# 7 Composition of Hoare Triples and Backlifting

## Introduction

In the last step, we finally proved the Hoare triples with the preconditions given in step 4. In this step, we will go all the way and compose all the Hoare triples together to one contract on the entire program. Then, we will prove equivalence of this to the ARM contract we originally phrased. Note that this means that everything BIR-related is outside the TCB. We only need to trust that the definitions in the ARM contract are valid.

The final theorems for the `add_reg`, `freuse` and `mutrec` examples are `arm_add_reg_contract_thm` in `tutorial_backliftingScript`, `bir_att_ct` in `freuse_compositionScript` and `bir_ieo_is_odd_ht` and `bir_ieo_is_even_ht` in `mutrec_compositionScript`, respectively.
