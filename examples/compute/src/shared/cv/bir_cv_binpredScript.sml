(* ------------------------------------------------------------------------- *)
(*  Definition of binary predicate evaluation and theorems associated        *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_cv_basicTheory ;
open bir_binpredTheory ;


val _ = new_theory "bir_cv_binpred" ;


(* Computes a general binary predicate with values as parameters *)
Definition bir_cv_compute_binpred_def:
  (bir_cv_compute_binpred binpred (SOME (BCVVal_Imm imm1)) (SOME (BCVVal_Imm imm2)) =
    (SOME (BCVVal_Imm (bool2b (bir_compute_binpred_imm binpred imm1 imm2))))) /\
  (bir_cv_compute_binpred _ _ _ = NONE)
End



(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)


Theorem bir_cv_compute_binpred_eq_compute_binpred:
  !binpred v1 v2. 
  (bir_cv_compute_binpred binpred v1 v2) = 
    (to_cv_val_option (bir_compute_binpred binpred (from_cv_val_option v1) (from_cv_val_option v2)))
Proof
  Cases_on `v1` >> Cases_on `v2` >| [
    ALL_TAC,
    ALL_TAC,
    Cases_on `x`,
    Cases_on `x` >> Cases_on `x'`
  ] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_binpred_def, bir_compute_binpred_def] >>
    rw [to_cv_val_option_def, to_cv_val_def]
QED



val _ = export_theory () ;
