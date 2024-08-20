(* ------------------------------------------------------------------------- *)
(*  Definition of ifthenelse expression evaluation and theorems associated   *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open bir_basicTheory bir_cv_basicTheory;
open bir_ifthenelseTheory;


val _ = new_theory "bir_cv_ifthenelse";


(* Computes an ifthenelse expression of two values *)
Definition bir_cv_compute_ifthenelse_def:
  bir_cv_compute_ifthenelse b v1 v2 = 
    if b = SOME bir_cvT then v1 
    else if b = SOME bir_cvF then v2
    else NONE
End



(* ------------------------------------------ *)
(* ---------------- THEOREMS ---------------- *)
(* ------------------------------------------ *)


(* compute and cv_compute are similar *)
Theorem bir_cv_compute_ifthenelse_eq_compute_ifthenelse:
  !b v1 v2.
    from_cv_val_option (bir_cv_compute_ifthenelse b v1 v2) =
      (bir_compute_ifthenelse (from_cv_val_option b) (from_cv_val_option v1) (from_cv_val_option v2))
Proof
  Cases_on `b` >> Cases_on `v1` >> Cases_on `v2` >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    rw [bir_cv_compute_ifthenelse_def, bir_compute_ifthenelse_def] >>
    rw [from_cv_val_option_def, from_cv_val_def] >>
    fs [bir_cvT_def, bir_cvF_def, birT_def, birF_def, from_cv_val_def] >>
    TRY (Cases_on `x`) >> fs [from_cv_val_def]
QED


val _ = export_theory ();
