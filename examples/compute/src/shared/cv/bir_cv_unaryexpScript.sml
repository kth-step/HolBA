(* ------------------------------------------------------------------------- *)
(*  Definition of unary expression evaluation and theorems associated        *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_cv_basicTheory ;
open bir_unaryexpTheory ;
open wordsTheory ;


val _ = new_theory "bir_cv_unaryexp" ;


(* Computes Unary expression *)
Definition bir_cv_compute_unaryexp_def:
  (bir_cv_compute_unaryexp unaryexp (SOME (BCVVal_Imm imm1)) = 
    (cv_val_from_imm_option (bir_compute_unaryexp_imm unaryexp imm1))) /\
  (bir_cv_compute_unaryexp _ _ = NONE)
End



(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)

(* compute and cv_compute are similar *)
Theorem bir_cv_compute_unaryexp_eq_compute_unaryexp:
  !unaryexp v. 
  from_cv_val_option (bir_cv_compute_unaryexp unaryexp v) = 
    (bir_compute_unaryexp unaryexp (from_cv_val_option v))
Proof
  Cases_on `v` >| [
    ALL_TAC,
    Cases_on `x`
  ] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_unaryexp_def, bir_compute_unaryexp_def] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    METIS_TAC [val_from_cv_val_option_from_imm_option]
QED


val _ = export_theory () ;
