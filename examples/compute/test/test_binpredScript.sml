open HolKernel Parse bossLib boolLib ;
open bir_basicTheory ;
open bir_binpredTheory ;


val _ = new_theory "test_binpred" ;


(* Equal predicate is reflexive *)
Theorem bir_eval_binpred_eq_refl:
    !env v. bir_eval_binpred BIExp_Equal (BVal_Imm v) (BVal_Imm v) birT
Proof
  Cases_on `v` >>
    rw [Once bir_eval_binpred_cases, bir_eval_binpred_imm_cases, bir_binpred_get_oper_def] >>
    rw [bool2b_T_eq_birT, bool2b_F_eq_birF]
QED



val _ = export_theory () ;
