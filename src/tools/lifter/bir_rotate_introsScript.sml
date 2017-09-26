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


val shift_neg1w_rewr3 = prove (
``~(-1w << n):'a word =
n2w
  (dimword (:'a) -
   ((dimword (:'a) - 2 ** n MOD dimword (:'a)) MOD dimword (:'a) + 1))``,
SIMP_TAC arith_ss [shift_neg1w_rewr2, word_1comp_n2w]);


val SHIFT_ZERO_bv = prove (
  ``(!a. a <<~ 0w = a) /\ (!a. a >>~ 0w = a) /\ (!a. a >>>~ 0w = a) /\
    (!a. a #<<~ 0w = a) /\ (!a. a #>>~ 0w = a)``,

  SIMP_TAC arith_ss [SHIFT_ZERO, word_lsl_bv_def, w2n_n2w, ZERO_LT_dimword,
    word_lsr_bv_def, word_asr_bv_def, word_rol_bv_def, word_ror_bv_def]);

val MOD_DIMINDEX_DIMWORD = prove (
``!m. ((m MOD dimindex (:'a)) MOD dimword (:'a)) =
      (m MOD dimindex (:'a))``,
GEN_TAC >>
`m MOD dimindex (:'a) < dimindex (:'a)` by
  ASM_SIMP_TAC arith_ss [DIMINDEX_GT_0] >>
`m MOD dimindex (:'a) < dimword (:'a)` by
  METIS_TAC [dimindex_lt_dimword, arithmeticTheory.LESS_TRANS] >>
ASM_SIMP_TAC arith_ss []);


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

val arm8_lsl_FOLD_GEN = prove (
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





val arm8_lsl_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 << (w2n w2 MOD dimindex (:'a))) = (w1 <<~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_lsl_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);


val arm8_lsl_no_imm_FOLDS = save_thm ("arm8_lsl_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsl_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end
  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)



(***********************)
(* FOLD "w >>>~ n2w x" *)
(***********************)

val arm8_lsr_FOLD_GEN = prove (
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



val arm8_lsr_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 >>> (w2n w2 MOD dimindex (:'a))) = (w1 >>>~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_lsr_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);


val arm8_lsr_no_imm_FOLDS = save_thm ("arm8_lsr_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsr_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end

  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)





(**********************)
(* FOLD "w >>~ n2w x" *)
(**********************)

val arm8_asr_FOLD_GEN = prove (
``!n (w:'a word).  n < dimindex (:'a) ==>

((((if word_bit (dimindex (:'a) - 1) w then -1w else 0w) &&
   ~~(-1w << (dimindex (:'a) - n))) || (w >>>~ n2w n)) =
(w >>~ n2w n))
``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
`dimindex (:'a) < dimword (:'a)` by METIS_TAC[dimindex_lt_dimword] >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [word_or_def, fcpTheory.FCP_BETA,
  word_and_def, WORD_NEG_1_T, word_0, word_lsl_def, word_asr_def,
  word_asr_bv_def, word_lsr_bv_def, w2n_n2w, GSYM word_msb,
  word_lsr_def, word_1comp_def, word_msb_def]);


val arm8_asr_FOLDS = save_thm ("arm8_asr_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_asr_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 33, inst ``:64`` 65, inst ``:16`` 17])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr3] thm1
  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [WORD_NEG_1, word_T_def, UINT_MAX_def,
    SHIFT_ZERO_bv] thm2
in
  thm3
end);



val arm8_asr_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 >> (w2n w2 MOD dimindex (:'a))) = (w1 >>~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_asr_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);


val arm8_asr_no_imm_FOLDS = save_thm ("arm8_asr_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_asr_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end

  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end);





(***************)
(* Combination *)
(***************)


val arm8_rotate_FOLDS = save_thm ("arm8_rotate_FOLDS",
  LIST_CONJ [arm8_lsl_FOLDS, arm8_and_neg_1w_FOLDS, arm8_lsr_FOLDS,
      arm8_asr_FOLDS, arm8_lsr_no_imm_FOLDS, arm8_asr_no_imm_FOLDS,
      arm8_lsl_no_imm_FOLDS])


val _ = export_theory();
