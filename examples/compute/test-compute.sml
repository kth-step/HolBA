(* ------------------------------------------------------------------------- *)
(*  Tests and sanity checks for the repository                               *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory bir_binexpTheory bir_evalTheory ;
open bir_binpredTheory ;
open bir_envTheory ;


(* ------------------------------------------------- *)
(* -------------------- bir_eval ------------------- *)
(* ------------------------------------------------- *)

val _ = prove(``
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)``,

  rw [Once bir_eval_exp_cases]) ;

val _ = prove(``
  !imm. bir_eval_exp bir_empty_env (BExp_Const imm) (BVal_Imm imm)``,

  rw [Once bir_eval_exp_cases]) ;

val _ = prove (``
  !env var vimm. bir_eval_exp (bir_env_update env var vimm) (BExp_Den var) vimm``, 

  Cases_on `var` >> Cases_on `env` >>
  rw [Once bir_eval_exp_cases, bir_env_update_def, bir_env_lookup_rel_def]) ;

val _ = prove (``
  !imm1 imm2. bir_eval_exp bir_empty_env 
    (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 imm1)) (BExp_Const (Imm64 imm2)))
    (BVal_Imm (Imm64 (imm1 + imm2)))``,

  rw [Ntimes bir_eval_exp_cases 3, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def] >>
  rw [Once bir_eval_exp_cases, bir_eval_binexp_def, bir_eval_binexp_imm_cases, bir_binexp_get_oper_def]) ;


(* ------------------------------------------------- *)
(* ------------------ bir_binpred ------------------ *)
(* ------------------------------------------------- *)

(* Equal predicate is reflexive *)
val _ = prove (``
  !env v. bir_eval_binpred BIExp_Equal (BVal_Imm v) (BVal_Imm v) birT``, 

  Cases_on `v` >>
    rw [Once bir_eval_binpred_cases, bir_eval_binpred_imm_cases, bir_binpred_get_oper_def] >>
    rw [bool2b_T_eq_birT, bool2b_F_eq_birF]) ;
