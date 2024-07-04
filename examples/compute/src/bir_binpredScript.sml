open HolKernel Parse boolLib bossLib
open bir_basicTheory


val _ = new_theory "bir_binpred"


(** Gets the operator for a given binary predicate *)
Definition bir_binpred_get_oper_def:
    (bir_binpred_get_oper BIExp_Equal = $=) /\
    (bir_binpred_get_oper BIExp_LessThan = word_lo)
End


(** Evaluates a binary predicate of two immediates *)
Inductive bir_eval_binpred_imm:
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm1 w1) (Imm1 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm8 w1) (Imm8 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm16 w1) (Imm16 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm32 w1) (Imm32 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm64 w1) (Imm64 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
    (!binpred w1 w2. 
        bir_eval_binpred_imm binpred (Imm128 w1) (Imm128 w2) ((bir_binpred_get_oper binpred) w1 w2))
End


(** Evaluates a general binary predicate with values as parameters *)
Inductive bir_eval_binpred:
    (!binpred imm1 imm2 b. 
        (bir_eval_binpred_imm binpred imm1 imm2 b) ==>
        (bir_eval_binpred binpred (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm (bool2b b))))
End


(** ***************** COMPUTE **************** *)

(** Computes a binary predicate of two immediates *)
Definition bir_compute_binpred_imm_def:
    (bir_compute_binpred_imm binpred (Imm1 w1) (Imm1 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred (Imm8 w1) (Imm8 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred (Imm16 w1) (Imm16 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred (Imm32 w1) (Imm32 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred (Imm64 w1) (Imm64 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred (Imm128 w1) (Imm128 w2) = (bir_binpred_get_oper binpred) w1 w2) /\
    (bir_compute_binpred_imm binpred _ _ = F)
End


(** Computes a general binary predicate with values as parameters *)
Definition bir_compute_binpred_def:
    (bir_compute_binpred binpred (SOME (BVal_Imm imm1)) (SOME (BVal_Imm imm2)) =
        SOME (BVal_Imm (bool2b (bir_compute_binpred_imm binpred imm1 imm2)))) /\
    (bir_compute_binpred _ NONE _ = NONE) /\
    (bir_compute_binpred _ _ NONE = NONE)
End



(* **************** THEOREMS ***************** *)
Theorem bir_eval_binpred_imp_compute_binpred:
    !binpred v1 v2 v. bir_eval_binpred binpred v1 v2 v ==> 
        bir_compute_binpred binpred (SOME v1) (SOME v2) = SOME v
Proof
    Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
        rw [bir_eval_binpred_cases, bir_compute_binpred_def] >>
        rw [bir_eval_binpred_imm_cases, bir_compute_binpred_imm_def] >>
        Cases_on `b` >> Cases_on `b'` >>
            rw [bool2b_def, bool2w_def, bir_compute_binpred_imm_def, bir_imm_t_nchotomy] >>
            fs [bir_eval_binpred_imm_cases] >>
            METIS_TAC []
QED











val _ = export_theory ()
