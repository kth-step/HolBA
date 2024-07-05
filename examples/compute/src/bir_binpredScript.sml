open HolKernel Parse boolLib bossLib ;
open bir_basicTheory ;
open bir_typingTheory ;


val _ = new_theory "bir_binpred" ;


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


(** If the term is well typed, then eval and compute are the same *)
Theorem well_typed_bir_eval_binpred_eq_compute_binpred:
    !binpred v1 v2 v. 
        (type_of_bir_val v1 = type_of_bir_val v2) ==>
    ( bir_eval_binpred binpred v1 v2 v <=> 
        bir_compute_binpred binpred (SOME v1) (SOME v2) = SOME v)
Proof
    Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
    rw [bir_eval_binpred_cases, bir_compute_binpred_def] >>
    rw [bir_eval_binpred_imm_cases, bir_compute_binpred_imm_def] >>
    Cases_on `b` >> Cases_on `b'` >>
        rw [bool2b_def, bool2w_def, bir_compute_binpred_imm_def, bir_imm_t_nchotomy] >>
        fs [bir_eval_binpred_imm_cases, type_of_bir_val_def, type_of_bir_imm_def] >>
        METIS_TAC []
QED


Theorem type_of_bir_val_imp_bir_eval_binpred:
    !binpred v1 v2.
        (type_of_bir_val v1 = type_of_bir_val v2) ==>
        ?v. bir_eval_binpred binpred v1 v2 v
Proof
    Cases_on `v1` >> Cases_on `v2` >>
    Cases_on `b` >> Cases_on `b'` >>
        rw [well_typed_bir_eval_binpred_eq_compute_binpred] >>
        rw [bir_compute_binpred_def, bir_compute_binpred_imm_def] >>
        fs [type_of_bir_val_def, type_of_bir_imm_def]
QED


Theorem bir_eval_binpred_correct_type:
    !binpred v1 v2 v ty.
        bir_eval_binpred binpred v1 v2 v ==>
        ((type_of_bir_val v1 = type_of_bir_val v2) /\ type_of_bir_val v = Bit1)
Proof
    Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
    Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
    rw [type_of_bir_val_def, bir_eval_binpred_cases, type_of_bir_imm_def, bir_eval_binpred_imm_cases, bool2b_def]
QED



Theorem bir_eval_binpred_eq_refl:
    !env v. bir_eval_binpred BIExp_Equal v v birT
Proof
    Cases_on `v` >> Cases_on `b` >>
        rw [Once bir_eval_binpred_cases, bir_eval_binpred_imm_cases, bir_binpred_get_oper_def] >>
        rw [bool2b_T_eq_birT, bool2b_F_eq_birF]
QED






val _ = export_theory () ;
