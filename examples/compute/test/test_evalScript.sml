(* ------------------------------------------------------------------------- *)
(*  Tests regarding the evaluation relation                                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib
open bir_basicTheory bir_binexpTheory bir_evalTheory open bir_envTheory

val _ = new_theory "test_eval"


Theorem bir_eval_exp_empty_env_const:
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)
Proof
  rw [Once bir_eval_exp_cases]
QED

Theorem bir_eval_exp_update_env_den:
  !env var vimm. bir_eval_exp (bir_env_update env var vimm) (BExp_Den var) vimm
Proof
  Cases_on `var` >> Cases_on `env` >>
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


val _ = export_theory ()
