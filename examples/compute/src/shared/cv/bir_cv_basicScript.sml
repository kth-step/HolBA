(* ------------------------------------------------------------------------- *)
(*  Basic type definition of BIR expressions                                 *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open wordsTheory;
open bir_basicTheory;
open alistTheory;

val _ = new_theory "bir_cv_basic";


(* Values for evaluation relation *)
Datatype:
  bir_cv_val_t = 
    BCVVal_Imm bir_imm_t
  | BCVVal_Mem bir_immtype_t bir_immtype_t ((num # num) list) (* Address Type / Value Type *)
End

(* BIR Expressions *)
Datatype:
  bir_cv_exp_t =
    BCVExp_Const bir_imm_t
  | BCVExp_MemConst bir_immtype_t bir_immtype_t ((num # num) list) (* Address Type / Value Type *)
  | BCVExp_Den bir_var_t

  | BCVExp_BinExp bir_binexp_t bir_cv_exp_t bir_cv_exp_t
  | BCVExp_UnaryExp bir_unaryexp_t bir_cv_exp_t

  | BCVExp_BinPred bir_binpred_t bir_cv_exp_t bir_cv_exp_t
  | BCVExp_IfThenElse bir_cv_exp_t bir_cv_exp_t bir_cv_exp_t

  (* Memory value / Address Value (Imm) / Endian / Type of where to load *)
  | BCVExp_Load bir_cv_exp_t bir_cv_exp_t bir_endian_t bir_immtype_t
  (* Memory value / Address Value (Imm) / Endian / Value to store *)
  | BCVExp_Store bir_cv_exp_t bir_cv_exp_t bir_endian_t bir_cv_exp_t
End


(* Booleans *)
Definition bir_cvT_def:
  bir_cvT = BCVVal_Imm (Imm1 1w)
End

Definition bir_cvF_def:
  bir_cvF = BCVVal_Imm (Imm1 0w)
End

(* Correction Theorems of boolean functions *)
Theorem bool2b_T_eq_bir_cvT:
  BCVVal_Imm (bool2b T) = bir_cvT
Proof
  rw [bool2b_def, bool2w_def, bir_cvT_def]
QED

Theorem bool2b_F_eq_birF:
  BCVVal_Imm (bool2b F) = bir_cvF
Proof
  rw [bool2b_def, bool2w_def, bir_cvF_def]
QED

Definition bir_cv_dest_bool_val_def:
  (bir_cv_dest_bool_val (BCVVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_cv_dest_bool_val _ = NONE)
End


(* ---------------------------------------- *)
(* -------------- CONVERSION -------------- *)
(* ---------------------------------------- *)

Definition cv_val_from_imm_option_def:
  (cv_val_from_imm_option NONE = NONE) /\
  (cv_val_from_imm_option (SOME imm) = SOME (BCVVal_Imm imm))
End

(* Converts a bir_cv_val_t to a bir_val_t *)
Definition from_cv_val_def:
  (from_cv_val (BCVVal_Imm imm) = BVal_Imm imm) /\
  (from_cv_val (BCVVal_Mem aty rty mmap_alist) = 
    (BVal_Mem aty rty (alist_to_fmap mmap_alist)))
End

(* WARNING : the to_cv_ variants aren’t computable through EVAL.
 * The existing conv from bir_cv_basicLib should be used instead.
 * Use only from_cv_ instead *)
Definition to_cv_val_def:
  (to_cv_val (BVal_Imm imm) = BCVVal_Imm imm) /\
  (to_cv_val (BVal_Mem aty rty mmap) = 
    (BCVVal_Mem aty rty (fmap_to_alist mmap)))
End

(* Wrapper conversion around option type *)
Definition from_cv_val_option_def:
  (from_cv_val_option NONE = NONE) /\
  (from_cv_val_option (SOME cv_val) = SOME (from_cv_val cv_val))
End

Definition to_cv_val_option_def:
  (to_cv_val_option NONE = NONE) /\
  (to_cv_val_option (SOME v) = SOME (to_cv_val v))
End

Definition from_cv_exp_def:
  (from_cv_exp (BCVExp_Const c) = BExp_Const c) /\
  (from_cv_exp (BCVExp_MemConst aty vty mmap_alist) = 
    (BExp_MemConst aty vty (alist_to_fmap mmap_alist))) /\
  (from_cv_exp (BCVExp_Den var) = BExp_Den var) /\
  (from_cv_exp (BCVExp_BinExp binexp e1 e2) = 
    (BExp_BinExp binexp (from_cv_exp e1) (from_cv_exp e2))) /\
  (from_cv_exp (BCVExp_UnaryExp unaryexp e) = 
    (BExp_UnaryExp unaryexp (from_cv_exp e))) /\
  (from_cv_exp (BCVExp_BinPred binpred e1 e2) = 
    (BExp_BinPred binpred (from_cv_exp e1) (from_cv_exp e2))) /\
  (from_cv_exp (BCVExp_IfThenElse e1 e2 e3) = 
    (BExp_IfThenElse (from_cv_exp e1) (from_cv_exp e2) (from_cv_exp e3))) /\
  (from_cv_exp (BCVExp_Load e1 e2 en rty) = 
    (BExp_Load (from_cv_exp e1) (from_cv_exp e2) en rty)) /\
  (from_cv_exp (BCVExp_Store e1 e2 en e3) = 
    (BExp_Store (from_cv_exp e1) (from_cv_exp e2) en (from_cv_exp e3)))
End

Definition to_cv_exp_def:
  (to_cv_exp (BExp_Const c) = BCVExp_Const c) /\
  (to_cv_exp (BExp_MemConst aty vty mmap) = 
    (BCVExp_MemConst aty vty (fmap_to_alist mmap))) /\
  (to_cv_exp (BExp_Den var) = BCVExp_Den var) /\
  (to_cv_exp (BExp_BinExp binexp e1 e2) = 
    (BCVExp_BinExp binexp (to_cv_exp e1) (to_cv_exp e2))) /\
  (to_cv_exp (BExp_UnaryExp unaryexp e) = 
    (BCVExp_UnaryExp unaryexp (to_cv_exp e))) /\
  (to_cv_exp (BExp_BinPred binpred e1 e2) = 
    (BCVExp_BinPred binpred (to_cv_exp e1) (to_cv_exp e2))) /\
  (to_cv_exp (BExp_IfThenElse e1 e2 e3) = 
    (BCVExp_IfThenElse (to_cv_exp e1) (to_cv_exp e2) (to_cv_exp e3))) /\
  (to_cv_exp (BExp_Load e1 e2 en rty) = 
    (BCVExp_Load (to_cv_exp e1) (to_cv_exp e2) en rty)) /\
  (to_cv_exp (BExp_Store e1 e2 en e3) = 
    (BCVExp_Store (to_cv_exp e1) (to_cv_exp e2) en (to_cv_exp e3)))
End


(* ---------------------------------------- *)
(* --------------- THEOREMS --------------- *)
(* ---------------------------------------- *)

Theorem val_from_cv_val_option_from_imm_option:
  !imm_opt. 
    from_cv_val_option (cv_val_from_imm_option imm_opt) =
      val_from_imm_option imm_opt
Proof
  Cases_on `imm_opt` >>
    rw[val_from_imm_option_def, from_cv_val_option_def, from_cv_val_def,
      cv_val_from_imm_option_def]
QED


Theorem from_to_cv_val:
  !v. from_cv_val (to_cv_val v) = v
Proof
  Cases_on `v` >>
    rw [from_cv_val_def, to_cv_val_def]
QED

Theorem from_to_cv_val_option:
  !v. from_cv_val_option (to_cv_val_option v) = v
Proof
  Cases_on `v` >>
    rw [from_cv_val_option_def, to_cv_val_option_def] >>
    rw [from_to_cv_val]
QED

Theorem from_to_cv_exp:
  !exp. from_cv_exp (to_cv_exp exp) = exp
Proof
  Induct_on `exp` >>
    rw [from_cv_exp_def, to_cv_exp_def]
QED

Theorem bir_cv_dest_bool_val_eq_dest_bool_val:
  !cv_val. bir_cv_dest_bool_val cv_val = 
    bir_dest_bool_val (from_cv_val cv_val)
Proof
  Cases_on `cv_val` >> 
  TRY (Cases_on `b`) >>
  rw [bir_cv_dest_bool_val_def, bir_dest_bool_val_def, from_cv_val_def]
QED


val _ = export_theory ();
