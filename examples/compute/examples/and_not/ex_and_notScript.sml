(* ------------------------------------------------------------------------- *)
(*  Example regarding a function that AND two boolean and returns            *)
(*  a variable or its negation                                               *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
open bir_basicTheory bir_envTheory
open bir_binexpTheory bir_ifthenelseTheory bir_unaryexpTheory
open bir_computeTheory
open wordsLib


val _ = new_theory "ex_and_not"

(* The variables used in the condition. They will be booleans *)
Definition var_cond1_def:
  var_cond1 = BVar "r1"
End

Definition var_cond2_def:
  var_cond2 = BVar "r2"
End

(* The variable we should return. Any size is fine *)
Definition var_ret_def:
  var_ret = BVar "r3"
End

(* Creates an environment where r1 is set to w *)
Definition start_env_def:
  start_env b1 b2 w = 
  bir_env_update (bir_env_update 
      (bir_env_update bir_empty_env var_ret (BVal_Imm (Imm64 w))) 
    var_cond1 (BVal_Imm (bool2b b1))) var_cond2 (BVal_Imm (bool2b b2))
End

Definition and_not_exp_def:
  and_not_exp = 
      BExp_IfThenElse (BExp_BinExp BIExp_And (BExp_Den var_cond1) (BExp_Den var_cond2)) 
        (BExp_Den var_ret) (BExp_UnaryExp BIExp_Not (BExp_Den var_ret))
End


(* ------------------------------------------------------------------------- *)
(* ------------------------------- THEOREMS -------------------------------- *)
(* ------------------------------------------------------------------------- *)

Theorem lookup_start_env_var_ret:
  !b1 b2 w. bir_env_lookup (start_env b1 b2 w) var_ret = SOME (BVal_Imm (Imm64 w))
Proof
  EVAL_TAC >>
  METIS_TAC []
QED


Theorem lookup_start_env_var_cond1:
  !b1 b2 w. bir_env_lookup (start_env b1 b2 w) var_cond1 = SOME (BVal_Imm (bool2b b1))
Proof
  EVAL_TAC >>
  METIS_TAC []
QED

Theorem lookup_start_env_var_cond2:
  !b1 b2 w. bir_env_lookup (start_env b1 b2 w) var_cond2 = SOME (BVal_Imm (bool2b b2))
Proof
  EVAL_TAC >>
  METIS_TAC []
QED


Theorem and_not_exp_correct:
  !b1 b2 w. bir_compute_exp and_not_exp (start_env b1 b2 w) = 
    SOME (BVal_Imm (Imm64 (if b1 /\ b2 then w else ~w)))
Proof
  Cases_on `b1` >> Cases_on `b2` >>
      EVAL_TAC >>
      METIS_TAC []
QED



val _ = export_theory ()
