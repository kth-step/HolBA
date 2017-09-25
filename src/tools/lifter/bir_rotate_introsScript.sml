open HolKernel Parse boolLib bossLib;
open wordsTheory

val _ = new_theory "bir_rotate_intros";


(*********************************)
(* Some silly auxiliary rewrites *)
(*********************************)

val shift_neg1w_rewr = prove (
``(-1w << n):'a word = -(n2w (2**n))``,
METIS_TAC[WORD_NEG_MUL, WORD_MUL_LSL, WORD_MULT_COMM])

val shift_neg1w_rewr2 = prove (
``(-1w << n):'a word = (n2w (dimword (:'a) - 2 ** n MOD dimword (:'a)))``,

SIMP_TAC std_ss [shift_neg1w_rewr] >>
SIMP_TAC std_ss [word_2comp_n2w]);


(***********************)
(* Evaluate "w && -1w" *)
(***********************)

val arm8_and_neg_1w_GEN = prove (``
  (!w:'a word. (w && -1w) = w) /\
  (!w:'a word. (-1w && w) = w)``,

SIMP_TAC std_ss [WORD_NEG_1, WORD_AND_CLAUSES]);


val arm8_and_neg_1w_FOLDS = save_thm ("arm8_and_neg_1w_FOLDS",
let
  fun inst wty =
    INST_TYPE [``:'a`` |-> wty] arm8_and_neg_1w_GEN;

  val thm1 = LIST_CONJ ([inst ``:32``, inst ``:64``, inst ``:16``])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_2comp_n2w] thm1
in
  thm2
end)


(***********************)
(* FOLD "w <<~ n2w x"  *)
(***********************)

val arm8_lsl_FOLD_GEN = store_thm ("arm8_lsl_FOLD_GEN",
``!n w.  n < dimword (:'a) ==>
(((((w:'a word) #>> (dimindex (:'a) - n)) && (-1w << n))) =
 (w <<~ n2w n))``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [word_and_def, fcpTheory.FCP_BETA,
  word_lsl_def, WORD_NEG_1_T, word_ror_def, word_lsl_bv_def, w2n_n2w,
  dimindex_lt_dimword] >>
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `i + dimindex (:'a) - n = dimindex (:'a) + (i - n)` SUBST1_TAC >- DECIDE_TAC >>
SIMP_TAC std_ss [DIMINDEX_GT_0, arithmeticTheory.ADD_MODULUS] >>
ASM_SIMP_TAC arith_ss []);


val arm8_lsl_FOLDS = save_thm ("arm8_lsl_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsl_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 32, inst ``:64`` 64, inst ``:16`` 16])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2] thm1
in
  thm2
end)


(***********************)
(* FOLD "w >>~ n2w x"  *)
(***********************)

val arm8_lsr_FOLD_GEN = store_thm ("arm8_lsr_FOLD_GEN",
``!n w.  n < dimword (:'a) ==>
(((((w:'a word) #>> n) && ~(-1w << (dimindex (:'a) - n)))) =
 (w >>>~ n2w n))``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [word_and_def, fcpTheory.FCP_BETA,
  word_lsr_def, WORD_NEG_1_T, word_ror_def, word_lsr_bv_def, w2n_n2w,
  dimindex_lt_dimword, word_lsl_def, arithmeticTheory.NOT_LESS_EQUAL,
  word_1comp_def]);


val arm8_lsr_FOLDS = save_thm ("arm8_lsr_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsr_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 32, inst ``:64`` 64, inst ``:16`` 16])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)


val _ = export_theory();
