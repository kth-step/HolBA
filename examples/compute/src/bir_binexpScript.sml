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

val _ = export_theory ()
