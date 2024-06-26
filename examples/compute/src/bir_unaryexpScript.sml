open HolKernel Parse bossLib boolLib
open bir_basicTheory
open wordsTheory


val _ = new_theory "bir_unaryexp"


(** Gets the operator for a given unary operation *)
Definition bir_unaryexp_get_oper_def:
    (bir_unaryexp_get_oper BIExp_Not = word_1comp) /\
    (bir_unaryexp_get_oper BIExp_ChangeSign = word_2comp)
End


(** Evaluates a binary expression of an immediate *)
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


(** Evaluates a general unary expression with values as parameters *)
Inductive bir_eval_unaryexp:
    (!unaryexp imm1 imm. 
        (bir_eval_unaryexp_imm unaryexp imm1 imm) ==>
        (bir_eval_unaryexp unaryexp (BVal_Imm imm1) (BVal_Imm imm)))
End

(** ****************** COMPUTE ****************** *)


(** Computes a binary expression of an immediate *)
Definition bir_compute_unaryexp_imm:
    (bir_compute_unaryexp_imm unaryexp (Imm1 w1) = SOME (BVal_Imm (Imm1 ((bir_unaryexp_get_oper unaryexp) w1)))) /\
    (bir_compute_unaryexp_imm unaryexp (Imm8 w1) = SOME (BVal_Imm (Imm8 ((bir_unaryexp_get_oper unaryexp) w1)))) /\
    (bir_compute_unaryexp_imm unaryexp (Imm16 w1) = SOME (BVal_Imm (Imm16 ((bir_unaryexp_get_oper unaryexp) w1)))) /\
    (bir_compute_unaryexp_imm unaryexp (Imm32 w1) = SOME (BVal_Imm (Imm32 ((bir_unaryexp_get_oper unaryexp) w1)))) /\
    (bir_compute_unaryexp_imm unaryexp (Imm64 w1) = SOME (BVal_Imm (Imm64 ((bir_unaryexp_get_oper unaryexp) w1)))) /\
    (bir_compute_unaryexp_imm unaryexp (Imm128 w1) = SOME (BVal_Imm (Imm128 ((bir_unaryexp_get_oper unaryexp) w1))))
End

(** Computes Unary expression *)
Definition bir_compute_unaryexp_def:
    (bir_compute_unaryexp unaryexp (SOME (BVal_Imm imm1)) = bir_compute_unaryexp_imm unaryexp imm1) /\
    (bir_compute_unaryexp _ NONE = NONE)
End


val _ = export_theory ()
