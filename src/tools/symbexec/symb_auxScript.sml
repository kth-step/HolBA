open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;

val _ = new_theory "symb_aux";

(* TODO: this should go to auxTheory *)
Theorem SUBSET_of_DIFF_thm:
  !s t v.
    s SUBSET t ==>
    ((s DIFF v) SUBSET (t DIFF v))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF]
QED

(* TODO: should go to BIR auxTheory *)
Theorem FUNPOW_OPT_SOME_thm:
  !f g.
   (!y. f y = SOME (g y)) ==>
   (!n x.
      (FUNPOW_OPT f n x = SOME (FUNPOW g n x)))
Proof
GEN_TAC >> GEN_TAC >> STRIP_TAC >>
  Induct_on `n` >- (
    REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW]
  ) >>
  REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW] >>
  ASM_SIMP_TAC std_ss [GSYM bir_auxiliaryTheory.FUNPOW_OPT_def]
QED

val _ = export_theory();
