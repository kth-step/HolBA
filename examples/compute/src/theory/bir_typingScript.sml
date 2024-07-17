(* ------------------------------------------------------------------------- *)
(*  Definition of the type system and the typing relation                    *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory ;
open bir_envTheory ;
open wordsTheory ;


val _ = new_theory "bir_typing" ;

(* Typing function for immediates *)
Definition type_of_bir_imm_def:
  (type_of_bir_imm (Imm1 w) = Bit1) /\
  (type_of_bir_imm (Imm8 w) = Bit8) /\
  (type_of_bir_imm (Imm16 w) = Bit16) /\
  (type_of_bir_imm (Imm32 w) = Bit32) /\
  (type_of_bir_imm (Imm64 w) = Bit64) /\
  (type_of_bir_imm (Imm128 w) = Bit128)
End

(* Typing function for values *)
Definition type_of_bir_val_def:
  (type_of_bir_val (BVal_Imm imm) = (BType_Imm (type_of_bir_imm imm))) /\
  (type_of_bir_val (BVal_Mem aty vty mmap) = (BType_Mem aty vty) )
End

(* Typing relation for bir expressions *)
Inductive type_of_bir_exp:
[~BExp_Const:]
  (!env imm. 
    type_of_bir_exp env (BExp_Const imm) (BType_Imm (type_of_bir_imm imm))) 

[~BExp_MemConst:]
  (!env aty vty mmap.
    type_of_bir_exp env (BExp_MemConst aty vty mmap) (BType_Mem aty vty) ) 

[~BExp_Den:]
  (!env var v.
    (bir_env_lookup_rel env var v)
    ==>
    type_of_bir_exp env (BExp_Den var) (type_of_bir_val v))

[~BExp_BinExp:]
  (!env binexp e1 e2 ty.
    (type_of_bir_exp env e1 (BType_Imm ty) /\ type_of_bir_exp env e2 (BType_Imm ty))
    ==>
    (type_of_bir_exp env (BExp_BinExp binexp e1 e2) (BType_Imm ty)))

[~BExp_UnaryExp:]
  (!env unaryexp e ty.
    (type_of_bir_exp env e (BType_Imm ty))
    ==>
    (type_of_bir_exp env (BExp_UnaryExp unaryexp e) (BType_Imm ty)))


[~BExp_BinPred:]
  (!env binpred e1 e2 ty.
    (type_of_bir_exp env e1 (BType_Imm ty) /\ type_of_bir_exp env e2 (BType_Imm ty))
    ==>
    (type_of_bir_exp env (BExp_BinPred binpred e1 e2) (BType_Imm Bit1)))

[~BExp_IfThenElse:]
  (!env epred e1 e2 ty.
    (type_of_bir_exp env e1 ty /\ type_of_bir_exp env e2 ty 
      /\ type_of_bir_exp env epred (BType_Imm Bit1))
    ==>
    (type_of_bir_exp env (BExp_IfThenElse epred e1 e2) ty))
End


Definition is_exp_well_typed_def:
  is_exp_well_typed env exp = ?ty. type_of_bir_exp env exp ty
End



(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)

(* 1 bit values are booleans *)
Theorem bit1_is_boolean:
  !v. type_of_bir_val v = (BType_Imm Bit1) ==> (v = birT \/ v = birF)
Proof
  Cases_on `v` >>
    Cases_on `b` >>
      rw [birT_def, birF_def, type_of_bir_val_def, type_of_bir_imm_def] >>
      Cases_on `c` >>
        fs [dimword_1]
QED

val _ = export_theory () ;
