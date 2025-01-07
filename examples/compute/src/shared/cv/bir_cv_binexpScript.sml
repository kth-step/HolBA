(* ------------------------------------------------------------------------- *)
(*  Definition of binary expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open birTheory bir_computeTheory bir_cv_basicTheory;
open wordsTheory;


val _ = new_theory "bir_cv_binexp";


(* Computes a general binary expression with values as parameters *)
Definition bir_cv_compute_binexp_def:
  (bir_cv_compute_binexp binexp (SOME (BCVVal_Imm imm1)) (SOME (BCVVal_Imm imm2)) =
    (cv_val_from_imm_option (bir_compute_binexp_imm binexp imm1 imm2))) /\
  (bir_cv_compute_binexp _ _ _ = NONE)
End



(* ------------------------------------------ *)
(* ---------------- THEOREMS ---------------- *)
(* ------------------------------------------ *)

(* compute and cv_compute are similar *)
Theorem bir_cv_compute_binexp_eq_compute_binexp:
  !binexp v1 v2. 
  from_cv_val_option (bir_cv_compute_binexp binexp v1 v2) = 
     (bir_compute_binexp binexp (from_cv_val_option v1) (from_cv_val_option v2))
Proof
  Cases_on `v1` >> Cases_on `v2` >| [
    all_tac,
    all_tac,
    Cases_on `x`,
    Cases_on `x` >> Cases_on `x'`
  ] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_binexp_def, bir_compute_binexp_def] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    metis_tac [val_from_cv_val_option_from_imm_option]
QED


val _ = export_theory ();
