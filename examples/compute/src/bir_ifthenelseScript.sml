open HolKernel Parse bossLib boolLib
open bir_basicTheory
open bir_typingTheory


val _ = new_theory "bir_ifthenelse"



Inductive bir_eval_ifthenelse:
[~BExp_IfThenElseT:]
    bir_eval_ifthenelse birT (v1:bir_val_t) (v2:bir_val_t) v1 

[~BExp_IfThenElseF:]
    bir_eval_ifthenelse birF v1 v2 v2
End

(* *********** COMPUTE ********** *)

Definition bir_compute_ifthenelse_def:
    bir_compute_ifthenelse b v1 v2 = 
        if b = SOME birT then v1 
        else if b = SOME birF then v2
        else NONE
End



(* ********* THEOREMS ************ *)

(* Typing Theorem *)
Theorem bir_eval_ifthenelse_keep_type:
    !v v1 v2 v3 ty.
        bir_eval_ifthenelse v v1 v2 v3 ==>
        (type_of_bir_val v1 = ty /\ type_of_bir_val v2 = ty) ==>
        (type_of_bir_val v = Bit1 <=> type_of_bir_val v3 = ty)
Proof
    Cases_on `v` >> Cases_on `v1` >> Cases_on `v2` >> Cases_on `v3` >>
    Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >> Cases_on `b'''` >>
    rw [type_of_bir_val_def, bir_eval_ifthenelse_cases, type_of_bir_imm_def,
        birT_def, birF_def]
QED




val _ = export_theory ()
