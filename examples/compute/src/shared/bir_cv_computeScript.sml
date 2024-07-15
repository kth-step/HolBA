(* ------------------------------------------------------------------------- *)
(*  Definition of the modified computation function for cv types             *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib ;
open bir_basicTheory bir_binexpTheory bir_unaryexpTheory bir_binpredTheory bir_ifthenelseTheory ;
open bir_cv_envTheory ;
open bir_computeTheory ;


val _ = new_theory "bir_cv_compute" ;

(* General Computation function *)
Definition bir_cv_compute_exp_def:
  (bir_cv_compute_exp (BExp_Const n) env = SOME (BVal_Imm n)) /\

  (* (bir_cv_compute (BExp_MemConst aty vty mmap) env = SOME (BVal_Mem aty vty mmap)) /\ *)

  (bir_cv_compute_exp (BExp_Den v) env = bir_cv_env_lookup env v) /\

  (* (bir_cv_compute (BExp_Cast ct e ty) env = ( *)
  (*    bir_eval_cast ct (bir_compute e env) ty)) /\ *)

  (bir_cv_compute_exp (BExp_UnaryExp et e) env = (
     bir_compute_unaryexp et (bir_cv_compute_exp e env))) /\

  (bir_cv_compute_exp (BExp_BinExp et e1 e2) env = (
     bir_compute_binexp et (bir_cv_compute_exp e1 env) (bir_cv_compute_exp e2 env))) /\

  (bir_cv_compute_exp (BExp_BinPred pt e1 e2) env = (
     bir_compute_binpred pt (bir_cv_compute_exp e1 env) (bir_cv_compute_exp e2 env))) /\
  (**)
  (* (bir_cv_compute (BExp_MemEq e1 e2) env = ( *)
  (*    bir_eval_memeq (bir_compute e1 env) (bir_compute e2 env))) /\ *)
  (**)
  (**)
  (bir_cv_compute_exp (BExp_IfThenElse c et ef) env =
     bir_compute_ifthenelse (bir_cv_compute_exp c env) (bir_cv_compute_exp et env) (bir_cv_compute_exp ef env)
  )
  (**)
  (* (bir_cv_compute (BExp_Load mem_e a_e en ty) env = *)
  (*    bir_eval_load (bir_compute mem_e env) (bir_compute a_e env) en ty) /\ *)
  (**)
  (* (bir_cv_compute (BExp_Store mem_e a_e en v_e) env = *)
  (*    bir_eval_store (bir_compute mem_e env) (bir_compute a_e env) en (bir_compute v_e env)) *)
End



Theorem bir_compute_exp_eq_cv_compute_exp:
  !cv_env e. bir_compute_exp e (to_env cv_env) = bir_cv_compute_exp e cv_env
Proof
  Induct_on `e` >>
    rw [bir_compute_exp_def, bir_cv_compute_exp_def] >>
    METIS_TAC [env_eq_to_env, env_eq_def]
QED



val _ = export_theory ()
