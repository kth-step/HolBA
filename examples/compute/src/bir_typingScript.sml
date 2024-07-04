open HolKernel Parse boolLib bossLib
open bir_basicTheory
open bir_envTheory
open wordsTheory


val _ = new_theory "bir_typing"

Definition type_of_bir_imm_def:
    (type_of_bir_imm (Imm1 w) = Bit1) /\
    (type_of_bir_imm (Imm8 w) = Bit8) /\
    (type_of_bir_imm (Imm16 w) = Bit16) /\
    (type_of_bir_imm (Imm32 w) = Bit32) /\
    (type_of_bir_imm (Imm64 w) = Bit64) /\
    (type_of_bir_imm (Imm128 w) = Bit128)
End

Definition type_of_bir_val_def:
    (type_of_bir_val (BVal_Imm imm) = type_of_bir_imm imm)
End

Inductive type_of_bir_exp:
[~BExp_Const:]
    (!env imm. 
        type_of_bir_exp env (BExp_Const imm) (type_of_bir_imm imm)) 

[~BExp_Den:]
    (!env var v.
        (bir_env_lookup_rel env var v)
        ==>
        type_of_bir_exp env (BExp_Den var) (type_of_bir_val v))

[~BExp_BinExp:]
    (!env binexp e1 e2 ty.
        (type_of_bir_exp env e1 ty /\ type_of_bir_exp env e2 ty)
        ==>
        (type_of_bir_exp env (BExp_BinExp binexp e1 e2) ty))

[~BExp_UnaryExp:]
    (!env unaryexp e ty.
        (type_of_bir_exp env e ty)
        ==>
        (type_of_bir_exp env (BExp_UnaryExp unaryexp e) ty))


[~BExp_BinPred:]
    (!env binpred e1 e2 ty.
        (type_of_bir_exp env e1 ty /\ type_of_bir_exp env e2 ty)
        ==>
        (type_of_bir_exp env (BExp_BinPred binpred e1 e2) Bit1))

[~BExp_IfThenElse:]
    (!env epred e1 e2 ty.
        (type_of_bir_exp env e1 ty /\ type_of_bir_exp env e2 ty 
            /\ type_of_bir_exp env epred Bit1)
        ==>
        (type_of_bir_exp env (BExp_IfThenElse epred e1 e2) ty))
End


Definition is_exp_well_typed_def:
    is_exp_well_typed env exp = ?ty. type_of_bir_exp env exp ty
End



(** ******* THEOREMS ********* *)

Theorem bit1_is_boolean:
    !v. type_of_bir_val v = Bit1 ==> (v = birT \/ v = birF)
Proof
    Cases_on `v` >>
    Cases_on `b` >>
        rw [birT_def, birF_def, type_of_bir_val_def, type_of_bir_imm_def] >>
        Cases_on `c` >>
            fs [dimword_1]
QED

val _ = export_theory ()
