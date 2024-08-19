(* ------------------------------------------------------------------------- *)
(*  Definition of binary expression evaluation and theorems associated       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory ;
open bir_typingTheory ;
open wordsTheory ;


val _ = new_theory "bir_binexp" ;


(* Gets the operator for a given binary operation *)
Definition bir_binexp_get_oper_def:
  (bir_binexp_get_oper BIExp_And = word_and) /\
  (bir_binexp_get_oper BIExp_Plus = word_add)
End


(* Evaluates a binary expression of two immediates *)
Inductive bir_eval_binexp_imm:
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm1 w1) (Imm1 w2) (Imm1 ((bir_binexp_get_oper binexp) w1 w2))) /\
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm8 w1) (Imm8 w2) (Imm8 ((bir_binexp_get_oper binexp) w1 w2))) /\
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm16 w1) (Imm16 w2) (Imm16 ((bir_binexp_get_oper binexp) w1 w2))) /\
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm32 w1) (Imm32 w2) (Imm32 ((bir_binexp_get_oper binexp) w1 w2))) /\
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm64 w1) (Imm64 w2) (Imm64 ((bir_binexp_get_oper binexp) w1 w2))) /\
  (!binexp w1 w2. 
    bir_eval_binexp_imm binexp (Imm128 w1) (Imm128 w2) (Imm128 ((bir_binexp_get_oper binexp) w1 w2)))
End


(* Evaluates a general binary expression with values as parameters *)
Definition bir_eval_binexp_def:
  (bir_eval_binexp binexp (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm imm) =
    (bir_eval_binexp_imm binexp imm1 imm2 imm)) /\
  (bir_eval_binexp _ _ _ _ = F)
End




(* ------------------------------------------ *)
(* ----------------- COMPUTE ---------------- *)
(* ------------------------------------------ *)

(* Computes a binary expression of two immediates *)
Definition bir_compute_binexp_imm_def:
  (bir_compute_binexp_imm BIExp_And (Imm1 w1) (Imm1 w2) = SOME (Imm1 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm8 w1) (Imm8 w2) = SOME (Imm8 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm16 w1) (Imm16 w2) = SOME (Imm16 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm32 w1) (Imm32 w2) = SOME (Imm32 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm64 w1) (Imm64 w2) = SOME (Imm64 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_And (Imm128 w1) (Imm128 w2) = SOME (Imm128 (word_and w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm1 w1) (Imm1 w2) = SOME (Imm1 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm8 w1) (Imm8 w2) = SOME (Imm8 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm16 w1) (Imm16 w2) = SOME (Imm16 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm32 w1) (Imm32 w2) = SOME (Imm32 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm64 w1) (Imm64 w2) = SOME (Imm64 (word_add w1 w2))) /\
  (bir_compute_binexp_imm BIExp_Plus (Imm128 w1) (Imm128 w2) = SOME (Imm128 (word_add w1 w2))) /\
  (bir_compute_binexp_imm binexp _ _ = NONE)
End


(* Computes a general binary expression with values as parameters *)
Definition bir_compute_binexp_def:
  (bir_compute_binexp binexp (SOME (BVal_Imm imm1)) (SOME (BVal_Imm imm2)) =
    val_from_imm_option (bir_compute_binexp_imm binexp imm1 imm2)) /\
  (bir_compute_binexp _ _ _ = NONE)
End



(* ------------------------------------------ *)
(* ---------------- THEOREMS ---------------- *)
(* ------------------------------------------ *)

(* Eval and compute are similar *)
Theorem bir_eval_binexp_eq_compute_binexp:
  !binexp v1 v2 v. bir_eval_binexp binexp v1 v2 v <=> 
    bir_compute_binexp binexp (SOME v1) (SOME v2) = SOME v
Proof
  Cases_on `binexp` >>
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
    rw [bir_eval_binexp_def, bir_compute_binexp_def] >>
    rw [bir_eval_binexp_imm_cases, bir_compute_binexp_imm_def] >>
    Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
      rw [bir_compute_binexp_imm_def, bir_imm_t_nchotomy, bir_binexp_get_oper_def] >>
      rw [val_from_imm_option_def] >>
      metis_tac []
QED


(* If the operands are typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_binexp:
  !binexp v1 v2 ty.
    ((type_of_bir_val v1 = BType_Imm ty) /\ (type_of_bir_val v2 = BType_Imm ty)) ==>
    ?v. bir_eval_binexp binexp v1 v2 v
Proof
  Cases_on `binexp` >>
  Cases_on `v1` >> Cases_on `v2` >>
  Cases_on `b` >> Cases_on `b'` >>
    rw [bir_eval_binexp_eq_compute_binexp] >>
    rw [bir_compute_binexp_def, bir_compute_binexp_imm_def] >>
    rw [val_from_imm_option_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def]
QED


(* Type conservation Theorem *)
Theorem bir_eval_binexp_keep_type:
  !binexp v1 v2 v ty.
    bir_eval_binexp binexp v1 v2 v ==>
    ((type_of_bir_val v1 = ty /\ type_of_bir_val v2 = ty) <=>
      type_of_bir_val v = ty)
Proof
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
    rw [type_of_bir_val_def, bir_eval_binexp_def, type_of_bir_imm_def, bir_eval_binexp_imm_cases]
QED






val _ = export_theory () ;
