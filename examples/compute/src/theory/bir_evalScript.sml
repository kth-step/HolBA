(* ------------------------------------------------------------------------- *)
(*  Definition of the general evaluation relation                            *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory bir_binexpTheory bir_unaryexpTheory bir_envTheory ;
open bir_binpredTheory bir_ifthenelseTheory ;


val _ = new_theory "bir_eval" ;


(* General evaluation relation of bir expressions *)
Inductive bir_eval_exp:
[~BExp_Const:]
  ( !env const. bir_eval_exp env (BExp_Const const) (BVal_Imm const) )

[~BExp_Den:]
  ( !env var. bir_env_lookup_rel env var v ==> bir_eval_exp env (BExp_Den var) v)

[~BExp_BinExp:]
  ( !env binexp e1 e2 v1 v2. 
    ((bir_eval_exp env e1 v1) /\ (bir_eval_exp env e2 v2) /\
      (bir_eval_binexp binexp v1 v2 v))
    ==> 
    (bir_eval_exp env (BExp_BinExp binexp e1 e2) v))

[~BExp_UnaryExp:]
  ( !env unaryexp e1 v1.  
    ((bir_eval_exp env e1 v1) /\
      (bir_eval_unaryexp unaryexp v1 v))
    ==> 
    (bir_eval_exp env (BExp_UnaryExp unaryexp e1) v))

[~BExp_BinPred:]
  (!env binpred e1 e2 v1 v2 b.
    ((bir_eval_exp env e1 v1) /\ (bir_eval_exp env e2 v2) /\
      (bir_eval_binpred binpred v1 v2 b))
    ==>
    (bir_eval_exp env (BExp_BinPred binpred e1 e2) b))

[~BExp_IfThenElse:]
  (!env epred e1 e2 v1 v2 v3.
    ((bir_eval_exp env epred v) /\
      (bir_eval_exp env e1 v1) /\ (bir_eval_exp env e2 v2) /\
      bir_eval_ifthenelse v v1 v2 v3)
    ==>
    (bir_eval_exp env (BExp_IfThenElse epred e1 e2) v3))

End






(* ****************************************** *)
(* ***************** TESTS ****************** *)
(* ****************************************** *)

Theorem bir_eval_exp_empty_env_const:
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)
Proof
  rw [Once bir_eval_exp_cases]
QED

Theorem bir_eval_exp_update_env_den:
  !env var vimm. bir_eval_exp (bir_env_update env var vimm) (BExp_Den var) vimm
Proof
  Cases_on `var` >>
  rw [Once bir_eval_exp_cases, bir_env_update_def, bir_env_lookup_rel_def] >>
  qexists_tac `s` >>
  rw [Once bir_eval_exp_cases, bir_env_update_def, bir_env_lookup_rel_def]
QED


Theorem bir_eval_exp_empty_env_add:
  !imm1 imm2. bir_eval_exp bir_empty_env 
    (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 imm1)) (BExp_Const (Imm64 imm2)))
    (BVal_Imm (Imm64 (imm1 + imm2)))
Proof
  rw [Ntimes bir_eval_exp_cases 3, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def] >>
  rw [Once bir_eval_exp_cases, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def]
QED




val _ = export_theory () ;
