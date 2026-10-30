open HolKernel boolLib Parse bossLib;

open wordsTheory wordsLib logrootTheory;

(* Arithmetic facts about integer square roots and 64-bit squaring,
   independent of the ARMv8 program *)

val _ = new_theory "isqrt_aux";

Theorem isqrt_sq_mono:
 !a b:num. a <= b ==> a * a <= b * b
Proof
 metis_tac [arithmeticTheory.LESS_MONO_MULT2]
QED

Theorem isqrt_ROOT_nat:
 !x n. x * x <= n /\ n < (x + 1) * (x + 1) <=> x = ROOT 2 n
Proof
 rpt gen_tac >> eq_tac >> strip_tac >- (
  CONV_TAC (REWR_CONV EQ_SYM_EQ) >> irule ROOT_UNIQUE >>
  fs [arithmeticTheory.ADD1]
 ) >>
 mp_tac (Q.SPECL [`2`, `n`] ROOT) >>
 fs [arithmeticTheory.ADD1]
QED

(* Squaring below 2^32 - 1 does not overflow *)
Theorem isqrt_w2n_sq:
 !x:word64. w2n x < 4294967295 ==>
  w2n (x * x) = w2n x * w2n x /\
  w2n ((x + 1w) * (x + 1w)) = (w2n x + 1) * (w2n x + 1)
Proof
 Cases >>
 REWRITE_TAC [w2n_n2w, word_mul_n2w, word_add_n2w] >>
 rpt strip_tac >>
 `n MOD dimword (:64) = n` by (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac []) >>
 FULL_SIMP_TAC bool_ss [] >>
 `n * n <= 4294967295 * 4294967295 /\
  (n + 1) * (n + 1) <= 4294967295 * 4294967295` by
   (conj_tac >> irule arithmeticTheory.LESS_MONO_MULT2 >> DECIDE_TAC) >>
 `(4294967295 * 4294967295:num) < dimword (:64)` by EVAL_TAC >>
 `n * n < dimword (:64) /\ (n + 1) * (n + 1) < dimword (:64)` by
   metis_tac [arithmeticTheory.LESS_EQ_LESS_TRANS] >>
 ASM_SIMP_TAC bool_ss [arithmeticTheory.LESS_MOD]
QED

val _ = export_theory ();
