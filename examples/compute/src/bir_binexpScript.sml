open HolKernel Parse bossLib boolLib
open bir_basicTheory
open wordsTheory


val _ = new_theory "bir_binexp"


(** Gets the operator for a given binary operation *)
Definition bir_binexp_get_oper_def:
    (bir_binexp_get_oper BIExp_And = word_and) /\
    (bir_binexp_get_oper BIExp_Plus = word_add)
End


(** Evaluates a binary expression of two immediates *)
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


(** Evaluates a general binary expression with values as parameters *)
Inductive bir_eval_binexp:
    (!binexp imm1 imm2 imm. 
        (bir_eval_binexp_imm binexp imm1 imm2 imm) ==>
        (bir_eval_binexp binexp (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm imm)))
End


(** ***************** COMPUTE **************** *)

(** Computes a binary expression of two immediates *)
Definition bir_compute_binexp_imm_def:
    (bir_compute_binexp_imm binexp (Imm1 w1) (Imm1 w2) = SOME (BVal_Imm (Imm1 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp (Imm8 w1) (Imm8 w2) = SOME (BVal_Imm (Imm8 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp (Imm16 w1) (Imm16 w2) = SOME (BVal_Imm (Imm16 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp (Imm32 w1) (Imm32 w2) = SOME (BVal_Imm (Imm32 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp (Imm64 w1) (Imm64 w2) = SOME (BVal_Imm (Imm64 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp (Imm128 w1) (Imm128 w2) = SOME (BVal_Imm (Imm128 ((bir_binexp_get_oper binexp) w1 w2)))) /\
    (bir_compute_binexp_imm binexp _ _ = NONE)
End


(** Computes a general binary expression with values as parameters *)
Definition bir_compute_binexp_def:
    (bir_compute_binexp binexp (SOME (BVal_Imm imm1)) (SOME (BVal_Imm imm2)) =
        bir_compute_binexp_imm binexp imm1 imm2) /\
    (bir_compute_binexp _ NONE _ = NONE) /\
    (bir_compute_binexp _ _ NONE = NONE)
End



(* **************** THEOREMS ***************** *)
Theorem bir_eval_binexp_eq_compute_binexp:
    !binexp v1 v2 v. bir_eval_binexp binexp v1 v2 v <=> 
        bir_compute_binexp binexp (SOME v1) (SOME v2) = SOME v
Proof
    Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
        rw [bir_eval_binexp_cases, bir_compute_binexp_def] >>
        rw [bir_eval_binexp_imm_cases, bir_compute_binexp_imm_def] >>
        Cases_on `b` >> Cases_on `b'` >>
            rw [bir_compute_binexp_imm_def, bir_imm_t_nchotomy] >>
            METIS_TAC []
QED


val _ = export_theory ()
