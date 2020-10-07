# 6 SMT Solver Used for Precondition Strengthening

## Introduction

From the previous steps, we derived some weakest preconditions from portions of the program and the related postconditions. Now, in order to prove that the corresponding Hoare triples `{P} prog {Q}` hold, we need to prove that `P ==> WP(prog,Q)`.

While multiple solutions exist to prove such predicates, SMT solvers offer a convenient and automatic way of doing so.

### Quick overview of SMT solvers

The Satisfiability Modulo Theories (SMT) problem is a decision problem for logical formulas over a set of theories. Common theories supported by SMT solvers include integers, real numbers, arithmetic, bit vectors or some data-structures such as lists or arrays.

A SMT instance is a quantifier-free first-order formula. When given a SMT instance, SMT solvers determine if the instance is _satisfiable_, i.e. if there exist a valuation for which the formula evaluates to true. The decision can be _satisfiable_ or _unsatisfiable_.

**Note**: SMT solvers can also decide _unknown_ if they run into an error.

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

In this tutorial, we will use the `Z3_ORACLE` solver, because we needed to add support for BIR memories and because `Z3` only works with Z3 2.x which is quite old (we are using Z3 4.x).

**Note**: Currently, the support for BIR memories works by using the array theory at the byte level. That's quite inefficient because BIR has some restrictions on memories that we could use (reads and writes are aligned). Moreover, we could add some axioms when translating to SMT-LIB 2.0 in order to consider loads and stores as only one operation instead of N operations (on N-byte words). Considering the exponential blow-up problem that arises when not using HolBA WP simplifier, this change could dramatically decrease the complexity of solving such instances in Z3.

## Proving Hoare triples

In the previous step of the tutorial, [5-wp](../5-wp), we obtained the weakest precondition for 4 portions of the program. We now want to verify than the corresponding Hoare triple hold. Assuming well-typedness and initialization, we have:

```
(P ==> WP(prog,Q)) ==> {P} prog {Q}
```

With a SMT solver, proving `not (P ==> WP(prog,Q))` to be _unsatisfiable_ is enough to prove the Hoare triple to hold.

**Note**: In logic, the predicate `A ==> B` is equivalent to `not A \/ B`.

## Step-by-step walk-through

### 1. Playing with Z3

Let's play with Z3 to see what SMT solvers are capable of. Open the file `tutorial-smt-playground.sml` and evaluate the header (from the top of the file until `"The fun starts here"`).

#### 1.1. Prove the truth to check that Z3 is working

First, let's prove the truth, ``T``, to see that Z3 is working. Now, let's see what is sent to Z3. To do so, raise the HolSmtLib's trace to 4 to keep temporary files. You should see something along those lines in the REPL:

```
<<HOL message: HolSmtLib: simplified goal is [] |- T>>
<<HOL message: HolSmtLib: calling external command '/some/path/to/HolBA_opt_dir/z3-4.8.4.d6df51951f4c/bin/z3 -smt2 -file:/tmp/MLTEMPrXDSxg > /tmp/MLTEMPHVRMBJ'>>
<<HOL message: HolSmtLib: solver reports negated term to be 'unsatisfiable' (no proof given)>>
val TRUTH = [oracles: HolSmtLib] [axioms: ] [] ⊢ T: thm
```

In the output above, `/tmp/MLTEMPrXDSxg` is the SMT-LIB 2.0 translation being sent to Z3, and `/tmp/MLTEMPHVRMBJ` contains Z3's answer, `unsat` in this case.

#### 1.2. The arithmetic theory

Now, let's try to prove the transitivity of the less operator for integers.

```sml
val LESS_TRANS = Z3_prove_or_print_model ``!m n p: int. m < n ∧ p < n ==> m < p``;
```

Evaluating this line will (of course) fail, and should give a counter-example:

```
<<HOL message: HolSmtLib: calling external command '...'>>
<<HOL message: HolSmtLib: solver reports negated term to be 'satisfiable' (no model given)>>
<<HOL message: Z3_with_modelLib: calling external command '...'>>
[v1_n = 0, v0_m = -1, v2_p = -1]
<<HOL message: Z3_with_modelLib: Z3 reports term to be 'satisfiable' (model given)>>
Failed to prove the given term. Here is a counter-example:
 - n: 0
 - m: -1
 - p: -1

Exception- HOL_ERR {message = "solver reports negated term to be 'satisfiable'", origin_function = "GENERIC_SMT_TAC", origin_structure = "HolSmtLib"} raised
```

Subtituing the given counter-example in the term that we want to prove gives: `-1 < 0 /\ -1 < 0 ==> -1 < -1`.... Oops! You can fix the term by swapping `p` and `n`.

#### 1.3. The bit-vector theory

HolBA being about binary analysis, let's use the bit-vector theory by proving that `x + 1 < x` with `x` a 32-bit word.

```sml
val INC_GREATER = Z3_prove_or_print_model ``!x: word32. x + 1w >+ x``;
```

**Note**: `>+` is the unsigned greater-than operator.

Damn, that failed again! Z3 gives `x = 0xFFFFFFFF` as a counter-example, which is 
`2^32 - 1`, i.e. the greatest representable value for unsigned 32-bit integers. If we substitute this in our term, we get `0xFFFFFFFF + 1 > 0xFFFFFFFF` or `0x00000000 > 0x7FFFFFFF`, or `0 > INT_MAX`. As we can see, 32-bit integers being bounded, they can wrap-around, meaning that our term is simply false for words. However, we can "fix" it by imposing that x is less than `INT_MAX`:

```sml
val INC_GREATER = Z3_prove_or_print_model ``!x: word32. x < 0xFFFFFFFFw ==> x + 1w >+ x``;
```

You can try using `>`, the unsigned greater-than operator. This will also fail because of a similar wrap-around problem.

#### 1.4. Proving BIR expressions

In order to prove BIR expressions, we need to tranlate it into the equivalent words expressions, because SMT solvers don't know about BIR. This is currently done using `bir_exp_to_wordsLib.bir2bool`:

```
> bir_exp_to_wordsLib.bir2bool (bandl [
    btrue,
    ble (bplus (bconstii 32 10, bconstii 32 8), bconstii 32 50)
  ]);
val it = “1w && (if 10w + 8w ≤₊ 50w then 1w else 0w) = 1w”: term
```

Now that we have a words expression, we know how to prove it. The example in this section should work without modification.

**Note**: The current solution in HolBA to turn BIR expressions to words expression is the non proof-producing `bir_exp_to_wordsLib` for time reasons. We are considering writing rewrite rules in order to have a proved translation.

### 2. Proving the Hoare triples

Now that we know how to use Z3, we don't want to have to invoke it by hand for each triple. To this end, we defined a function `prove_exp_is_taut` that takes a BIR expression and prove that it is a BIR tautology. We now need to prove that it is a tautology because in the previous section we assumed well-typedness and intialization.

Open the file `tutorial_smtScript.sml` and evaluate the header (from the top of the file until `new_theory "tutorial_smt"`).

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

