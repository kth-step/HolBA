(* ------------------------------------------------------------------------- *)
(*  Definition of unary expression evaluation and theorems associated        *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory ;
open bir_typingTheory ;
open wordsTheory ;


val _ = new_theory "bir_unaryexp" ;


(* Gets the operator for a given unary operation *)
Definition bir_unaryexp_get_oper_def:
  (bir_unaryexp_get_oper BIExp_Not = word_1comp) /\
  (bir_unaryexp_get_oper BIExp_ChangeSign = word_2comp)
End


(* Evaluates a binary expression of an immediate *)
Inductive bir_eval_unaryexp_imm:
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm1 w1) (Imm1 ((bir_unaryexp_get_oper unaryexp) w1))) /\
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm8 w1) (Imm8 ((bir_unaryexp_get_oper unaryexp) w1))) /\
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm16 w1) (Imm16 ((bir_unaryexp_get_oper unaryexp) w1))) /\
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm32 w1) (Imm32 ((bir_unaryexp_get_oper unaryexp) w1))) /\
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm64 w1) (Imm64 ((bir_unaryexp_get_oper unaryexp) w1))) /\
  (!unaryexp w1. 
    bir_eval_unaryexp_imm unaryexp (Imm128 w1) (Imm128 ((bir_unaryexp_get_oper unaryexp) w1)))
End


(* Evaluates a general unary expression with values as parameters *)
Definition bir_eval_unaryexp_def:
  (bir_eval_unaryexp unaryexp (BVal_Imm imm1) (BVal_Imm imm) =
    (bir_eval_unaryexp_imm unaryexp imm1 imm)) /\
  (bir_eval_unaryexp _ _ _ = F)
End

(* ****************************************** *)
(* ***************** COMPUTE **************** *)
(* ****************************************** *)


(* Computes a binary expression of an immediate *)
Definition bir_compute_unaryexp_imm_def:
  (bir_compute_unaryexp_imm BIExp_Not (Imm1 w1) = SOME (Imm1 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm8 w1) = SOME (Imm8 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm16 w1) = SOME (Imm16 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm32 w1) = SOME (Imm32 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm64 w1) = SOME (Imm64 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_Not (Imm128 w1) = SOME (Imm128 (word_1comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm1 w1) = SOME (Imm1 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm8 w1) = SOME (Imm8 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm16 w1) = SOME (Imm16 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm32 w1) = SOME (Imm32 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm64 w1) = SOME (Imm64 (word_2comp w1))) /\
  (bir_compute_unaryexp_imm BIExp_ChangeSign (Imm128 w1) = SOME (Imm128 (word_2comp w1)))
End

(* Computes Unary expression *)
Definition bir_compute_unaryexp_def:
  (bir_compute_unaryexp unaryexp (SOME (BVal_Imm imm1)) = 
    val_from_imm_option (bir_compute_unaryexp_imm unaryexp imm1)) /\
  (bir_compute_unaryexp _ _ = NONE)
End



(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)


(* Eval and Compute are similar *)
Theorem bir_eval_unaryexp_eq_compute_unaryexp:
  !unaryexp v1 v. bir_eval_unaryexp unaryexp v1 v <=> 
    bir_compute_unaryexp unaryexp (SOME v1) = SOME v
Proof
  Cases_on `unaryexp` >>
  Cases_on `v1` >> Cases_on `v` >>
    rw [bir_eval_unaryexp_def, bir_compute_unaryexp_def] >>
    rw [bir_eval_unaryexp_imm_cases, bir_compute_unaryexp_imm_def] >>
    Cases_on `b` >> Cases_on `b'` >>
      rw [bir_compute_unaryexp_imm_def, bir_imm_t_nchotomy, bir_unaryexp_get_oper_def] >>
      rw [val_from_imm_option_def] >>
      METIS_TAC []
QED


(* Unary_exp always evaluates *)
Theorem type_of_bir_val_imp_bir_eval_unaryexp:
  !unaryexp v ty.
    (type_of_bir_val v = BType_Imm ty) ==>
    ?v'. bir_eval_unaryexp unaryexp v v'
Proof
  Cases_on `unaryexp` >>
  Cases_on `v` >>
  Cases_on `b` >>
    rw [bir_eval_unaryexp_eq_compute_unaryexp, type_of_bir_val_def] >>
    rw [bir_compute_unaryexp_def, bir_compute_unaryexp_imm_def] >>
    rw [val_from_imm_option_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def]
QED


(* Type conservation theorem *)
Theorem bir_eval_unaryexp_keep_type:
  !unaryexp v1 v2 ty.
    bir_eval_unaryexp unaryexp v1 v2 ==>
    (type_of_bir_val v1 = type_of_bir_val v2)
Proof
  Cases_on `v1` >> Cases_on `v2` >>
  Cases_on `b` >> Cases_on `b'` >>
    rw [type_of_bir_val_def, bir_eval_unaryexp_def, type_of_bir_imm_def, bir_eval_unaryexp_imm_cases]
QED

val _ = export_theory () ;
