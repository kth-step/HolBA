# Tutorial - 6. SMT solver

## Introduction

From the previous steps, we derived some weakest preconditions from portions of the program and the related postconditions. Now, in order to prove that the corresponding Hoare triples `{P} prog {Q}` hold, we need to prove that `P ==> WP(prog,Q)`.

While multiple solutions exist to prove such predicates, SMT solvers offer a convenient and automatic way of doing so.

### Quick overview of SMT solvers

The Satisfiability Modulo Theories (SMT) problem is a decision problem for logical formulas over a set of theories. Common theories supported by SMT solvers include integers, real numbers, arithmetic, bit vectors or some data-structures such as lists or arrays.

A SMT instance is a quantifier-free first-order formula. When given a SMT instance, SMT solvers determine if the instance is _satisfiable_, i.e. if there exist a valuation for which the formula evaluates to true. The decision can be _satisfiable_ or _unsatisfiable_.

**Note**: SMT cal also decide `unknown` if they run into an error.

In our use case, we want to prove that a given boolean formula is true. This is equivalent to determining if there are no valuation for which it is false, which translate in SMT solver terms in proving that the negation of the formula is _unsatifiable_.

### Using SMT solvers in HOL4

HOL4 comes with a library for integrating SMT solvers inside HOL4 called [HolSmtLib](https://github.com/HOL-Theorem-Prover/HOL/blob/kananaskis-12/src/HolSmt/HolSmtLib.sig). It provides interfaces to Yices and Z3, and also provides a third proof-producing sovler backed by Z3. For each interface, HolSmtLib provides two functions: `val [SOLVER]_TAC: tactic` and `val [SOLVER]_PROVE: term -> thm`.

The first two solvers, called `YICES` and `Z3_ORACLE`, work by first translating the **negated** goal and assumption list into an equivalent representation using an intermediate language (SMT-LIB 2.0 in the case of Z3) in a non proof-producing way, query the SMT solver, and prove the goal using an oracle if the SMT solver reports _unsatisfiable_.

**Note**: In order to see the tags left by the oracles in proved theorems, you can turn on tag printing: 

```sml
val _ = Globals.show_tags := true;
```

_[end of note]_

The third solver, simply called `Z3`, asks Z3 for a proof procedure to prove the term directly in HOL4. Hence, it doesn't need to use an oracle.

In this tutorial, we will use the `Z3_ORACLE` solver, because we needed to add support for arrays and because `Z3` only works with Z3 2.x.

## Proving Hoare triples

In the previous step of the tutorial, [5-wp](../5-wp), we obtained the weakest precondition for 4 portions of the program. We now want to verify than the corresponding Hoare triple hold. Assuming well-typedness and initialization, we have:

```
(P ==> WP(prog,Q)) ==> {P} prog {Q}
```

With a SMT solver, proving `not (P ==> WP(prog,Q))` to be _unsatisfiable_ is enough to prove the Hoare triple to hold.

**Note**: In logic, the predicate `A ==> B` is equivalent to `not A \/ B`.

## Step-by-step walk-through

### 1. Playing with Z3

BIR PP

### 2. Proving the Hoare triples

Now that we know how to use Z3, we don't want to have to invoke it by hand for each triple. To this end, we defined a function `prove_exp_is_taut` that takes a BIR expression and prove that it is a BIR tautology. We now need to prove that it is a tautology because in the previous section we assumed well-typedness and intialization.

Open the file `tutorial_smtScript.sml` and execute the header (from the top of the file until the `new_theory "tutorial_smt"`).

You should know how to proceed by now. Each triple is delimited by horizontal comment separators. For readibility, for each contract, we create a few variables:

* `contract_N_pre: term`: precondition (BIR expression)
* `contract_N_wp: term`: generated weakest precondition (idem)
* `contract_N_imp: term`: `contract_N_pre ==> contract_N_wp` (idem)
* `contract_N_imp_taut_thm: thm`: a theorem stating that `contract_N_imp` is a tautology, proved using Z3.

**Note**: If you want to see the value of a HOL4 definition, you can evaluate `[definition_name]_def` in the REPL. That's a convention in HolBA that definitions are stored in variables following the naming scheme. If the definition uses another definition, just apply the same method. For example, try evaluating `bir_add_reg_contract_1_pre_def`. Another solution is to use `EVAL`:

```sml
EVAL ``bir_add_reg_contract_1_pre``
```

This evaluates all definitions and shows the expected result. However, this can lead to huge expression or infinite rewrite in some cases. See [`bossLib.EVAL`](https://hol-theorem-prover.org/kananaskis-12-helpdocs/help/Docfiles/HTML/bossLib.EVAL.html) in HOL4 documentation for more details.

_[end of note]_

