# 4 Contracts and From BIR to ARM
We use registers ``4`` and ``5`` to refer to the original values of
the input parameters, since these registers are never updated. 
The precondition for our function is:
```
arm8_add_reg_pre m ⇔
m.REG 4w ≥ 0w ∧ (m.REG 4w = m.REG 2w) ∧ (m.REG 5w = m.REG 3w)
```
I.e. the initial value of register 4 is equal to register 2, and
register 5 is equal to register 3. Moreover. register 4 should be
non-negative. If the input `x` is negative, then we do not enter
the loop and we do not compute the right sum.

The postcondition is trivial:
```
arm8_add_reg_post m ⇔ (m.REG 4w + m.REG 5w = m.REG 3w)
```
The final value of register 3 should be equal to R4+R5.

The same precondition and postconditions are defined for BIR. The
language is a bit verbose (it is not intended to be directly
written by humans). We have a small DSL that simplify it's
definition a bit:
```
val get_y = bden (bvar "R5" ``(BType_Imm Bit64)``);
val get_x = bden (bvar "R4" ``(BType_Imm Bit64)``);
val get_ly = bden (bvar "R3" ``(BType_Imm Bit64)``);
val get_lx = bden (bvar "R2" ``(BType_Imm Bit64)``);
val get_sp = bden (bvar "SP_EL0" ``(BType_Imm Bit64)``);
val get_r0 = bden (bvar "R0" ``(BType_Imm Bit64)``);

bandl [bnot (bslt(get_x, bconst64 0)),
       beq(get_lx, get_x),
       beq(get_ly, get_y)
      ]
```
Generates the precondition:
```
bir_add_reg_pre =
     BExp_BinExp BIExp_And
       (BExp_BinExp BIExp_And
          (BExp_UnaryExp BIExp_Not
             (BExp_BinPred BIExp_SignedLessThan
                (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                (BExp_Const (Imm64 0w))))
          (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R2" (BType_Imm Bit64)))
             (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
       (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R3" (BType_Imm Bit64)))
          (BExp_Den (BVar "R5" (BType_Imm Bit64))))
```

## Hoare triple
Internally, the tools uses several definitions for Hoare triples (due
to different needs). The one that we are using here is defined in terms
of the `weak_triple` from `bin_hoare_logicTheory`:
```
∀mms l ls pre post.
  arm8_triple mms l ls pre post ⇔
  weak_triple arm_weak_model l ls
    (λms.
	 arm8_bmr.bmr_extra ms ∧
	 EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ∧ pre ms)
    (λms.
	 arm8_bmr.bmr_extra ms ∧
	 EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ∧ post ms)
```

There is a similar formulation for BIR:
```
∀prog l ls pre post.
  bir_triple prog l ls pre post ⇔
  weak_triple (bir_etl_wm prog) l ls
    (λs. bir_exec_to_labels_triple_precond s pre prog)
    (λs'. bir_exec_to_labels_triple_postcond s' post prog)
```
where
```
∀st pre prog.
  bir_exec_to_labels_triple_precond st pre prog ⇔
  (bir_eval_exp pre st.bst_environ = SOME bir_val_true) ∧
  bir_env_vars_are_initialised st.bst_environ (bir_vars_of_program prog) ∧
  (st.bst_pc.bpc_index = 0) ∧ (st.bst_status = BST_Running) ∧
  bir_is_bool_exp_env st.bst_environ pre
```
Notice that the main difference between the BIR and ARM contract is
that the BIR contract applies only for
states that enable the evaluation of the program: i.e. they have all
variables of the program initialized. BIR programs produced by the
lifter always uses the same set of variables (i.e. `MEM`, `R0`, etc).
However, program transformations and hand crafted BIR could use other
variables. Similarly, the precondition may constraints the value of
some variables that are never used by the program.

`bir_exec_to_labels_triple_postcond` is defined similarly, the only
difference being that the postcondition `post` is a function from
labels, so it is applied on the label of the state argument `st`.

## Loop invariant
The standard loop invariant for our program should be
```
x0+y0 = x+y /\ x>=0
```
The condition `x>=0` is needed to ensure that `x0+y0 = y` when the
while condition does not hold (i.e. `x <= 0`).
When dealing with binary programs things get a bit more complicated.
The conditional jump exits the loop when the following condition holds
```
(BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not
      (BExp_BinPred BIExp_Equal
	 (BExp_Den (BVar "ProcState_N" BType_Bool))
	 (BExp_Den (BVar "ProcState_V" BType_Bool))))
   (BExp_Den (BVar "ProcState_Z" BType_Bool)))
```
Therefore the code before the loop and the end of the loop body must
ensure that this expression (i.e. the flags) is equivalent to 
`x <= 0`. For this reason the loop invariant is defined as:
```
bandl [beq (bplus(get_y, get_x), bplus(get_ly, get_lx)),
       bsle(bconst64 0, get_lx),
       beq (original_add_reg_loop_condition, bir_add_reg_loop_condition)
      ]
```
where 
```
val original_add_reg_loop_condition =  (bnot (bsle(get_lx, bconst64 0)));
```

TODO refer to the blocks of the figure

## Contract for fragment 1
The fragment from `0x38` to `0x40` (excluded) computes the while
condition.
Its precondition is simply `bir_add_reg_pre` and its postcondition is
the loop invariant.

## Contract for fragment 2
The fragment from `0x20` to `0x40` (excluded) is the loop body
(including the update of the while condition.
To ensure that the loop terminates, we must additionally provide a
variant. In this case, the variant is simply `lx`, which is stored in
the register `x2`.
Therefore the precondition (the version with `v`) is
```
bandl [``bir_add_reg_I``,
       bir_add_reg_loop_condition,
       beq(get_lx, ``(BExp_Const (Imm64 v))``)
      ]
```
and the postcondition is
```
bandl [``bir_add_reg_I``,
       bnot(bsle(``(BExp_Const (Imm64 v))``, get_lx)),
       bsle(bconst64 0, get_lx)
      ]
```
Notice that we use a free variable (i.e. `v`) to bind the initial
value of the register. We could have used the same approach to save
the initial value of the two parameters. This is a HOL4 variable, not
a BIR variable.


## Contract for fragment 3
The third fragment (`0x40` to `0x20`) is the loop-continue case. It only consists of one
instruction capture the cases when the loop condition holds.
Therefore its precondiiton is
```
band(``bir_add_reg_I``, bir_add_reg_loop_condition)
```
This is also the fragment postcondition, since this fragment has no
affect to the state variables.


## Contract for fragment 4
The last fragment (`0x40` to `0x4c`) is the loop-exit case. It only
consists of the conditional jump when when the loop condition does not
hold and all subsequent instructions.
Therefore its precondiiton is
```
band(``bir_add_reg_I``, bnot bir_add_reg_loop_condition)
```
and its postcondition is the function postcondition:
```
bir_add_reg_post
```


## From BIR to ARM
To enable transfer of properties from ARM to BIR and vice versa we must
demonstrate that the contracts are equivalent.

We first demonstrate that the BIR precondition is a boolean
expression:
```
bir_is_bool_exp bir_add_reg_pre
```

Then we use a set of simplification rules (i.e. `arm_to_bir_exp_thms`)
and demonstrate that 
```
bir_pre_arm8_to_bir arm8_add_reg_pre bir_add_reg_pre
```
and
```
bir_post_bir_to_arm8 arm8_add_reg_post bir_add_reg_post
```

Definition of these two predicates is straightforward:
```
bir_pre_arm8_to_bir pre pre_bir ⇔
  bir_is_bool_exp pre_bir ∧
  ∀ms bs.
      bmr_rel arm8_bmr bs ms ⇒
      bir_env_vars_are_initialised bs.bst_environ
	(bir_vars_of_exp pre_bir) ⇒
      pre ms ⇒
      (bir_eval_exp pre_bir bs.bst_environ = bir_val_true)
```
and
```
∀post post_bir ls.
  bir_post_bir_to_arm8 post post_bir ls ⇔
  ∀ms bs l.
      l ∈ ls ⇒
      bmr_rel arm8_bmr bs ms ⇒
      (bir_eval_exp (post_bir l) bs.bst_environ = SOME bir_val_true) ⇒
      post ms
```
