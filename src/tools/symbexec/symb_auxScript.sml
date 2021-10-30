open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;

val _ = new_theory "symb_aux";

(* TODO: this should go to auxTheory *)
val SUBSET_of_DIFF_thm = store_thm(
   "SUBSET_of_DIFF_thm",
  ``!s t v.
    s SUBSET t ==>
    ((s DIFF v) SUBSET (t DIFF v))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF]
);

(* TODO: should go to BIR auxTheory *)
val FUNPOW_OPT_SOME_thm = store_thm(
   "FUNPOW_OPT_SOME_thm", ``
!f g.
   (!y. f y = SOME (g y)) ==>
   (!n x.
      (FUNPOW_OPT f n x = SOME (FUNPOW g n x)))
``,
  GEN_TAC >> GEN_TAC >> STRIP_TAC >>
  Induct_on `n` >- (
    REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW]
  ) >>
  REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW] >>
  ASM_SIMP_TAC std_ss [GSYM bir_auxiliaryTheory.FUNPOW_OPT_def]
);

val _ = export_theory();
