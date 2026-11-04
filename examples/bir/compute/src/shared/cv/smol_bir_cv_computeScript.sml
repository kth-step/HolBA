(* ------------------------------------------------------------------------- *)
(*  Definition of the modified computation function for cv types             *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open smol_bir_cv_basicTheory smol_bir_cv_binexpTheory smol_bir_cv_unaryexpTheory smol_bir_cv_binpredTheory smol_bir_cv_ifthenelseTheory;
open smol_bir_cv_memTheory;
open smol_bir_cv_envTheory;
open smol_bir_computeTheory;
open wordsLib cv_transLib cv_stdTheory cvTheory;


val _ = new_theory "smol_bir_cv_compute";

(* cv_stdTheory has ratTheory as ancestor, which makes numerals default to rat;
   prefer num again, here and in descendant theories *)
val _ = numLib.prefer_num ();

(* General Computation function *)
Definition bir_cv_compute_exp_def:
  (bir_cv_compute_exp (BCVExp_Const n) env = SOME (BCVVal_Imm n)) /\

  (bir_cv_compute_exp (BCVExp_MemConst aty vty mmap) env = SOME (BCVVal_Mem aty vty mmap)) /\

  (bir_cv_compute_exp (BCVExp_Den v) env = bir_cv_env_lookup env v) /\

  (* (bir_cv_compute (BExp_Cast ct e ty) env = ( *)
  (*    bir_eval_cast ct (bir_compute e env) ty)) /\ *)

  (bir_cv_compute_exp (BCVExp_UnaryExp et e) env = (
     bir_cv_compute_unaryexp et (bir_cv_compute_exp e env))) /\

  (bir_cv_compute_exp (BCVExp_BinExp et e1 e2) env = (
     bir_cv_compute_binexp et (bir_cv_compute_exp e1 env) (bir_cv_compute_exp e2 env))) /\

  (bir_cv_compute_exp (BCVExp_BinPred pt e1 e2) env = (
     bir_cv_compute_binpred pt (bir_cv_compute_exp e1 env) (bir_cv_compute_exp e2 env))) /\
  (**)
  (* (bir_cv_compute (BExp_MemEq e1 e2) env = ( *)
  (*    bir_eval_memeq (bir_compute e1 env) (bir_compute e2 env))) /\ *)
  (**)
  (**)
  (bir_cv_compute_exp (BCVExp_IfThenElse c et ef) env =
     bir_cv_compute_ifthenelse (bir_cv_compute_exp c env) (bir_cv_compute_exp et env) (bir_cv_compute_exp ef env)
  ) /\

  (bir_cv_compute_exp (BCVExp_Load mem_e a_e en ty) env =
     bir_cv_compute_load (bir_cv_compute_exp mem_e env) (bir_cv_compute_exp a_e env) en ty) /\

  (bir_cv_compute_exp (BCVExp_Store mem_e a_e en v_e) env =
     bir_cv_compute_store (bir_cv_compute_exp mem_e env) (bir_cv_compute_exp a_e env) en (bir_cv_compute_exp v_e env))
End



Theorem bir_compute_exp_eq_cv_compute_exp:
  !cv_env cv_e. bir_compute_exp (from_cv_exp cv_e) (from_cv_env cv_env) = 
    from_cv_val_option (bir_cv_compute_exp cv_e cv_env)
Proof
  Induct_on `cv_e` >>
    rw [from_cv_exp_def] >>
    rw [bir_compute_exp_def, bir_cv_compute_exp_def] >| [

      (* BCVExp_Const *)
      rw [from_cv_val_option_def, from_cv_val_def],

      (* BCVExp_MemConst *)
      rw [from_cv_val_option_def, from_cv_val_def],

      (* BCVExp_Den *)
      metis_tac [env_eq_from_cv_env, env_eq_def],

      (* BCVExp_BinExp *)
      rw [bir_cv_compute_binexp_eq_compute_binexp] >>
      rw [from_to_cv_val_option], 

      (* BCVExp_UnaryExp *)
      rw [bir_cv_compute_unaryexp_eq_compute_unaryexp] >>
      rw [from_to_cv_val_option], 

      (* BCVExp_BinPred *)
      rw [bir_cv_compute_binpred_eq_compute_binpred] >>
      rw [from_to_cv_val_option], 

      (* BCVExp_IfThenElse *)
      rw [bir_cv_compute_ifthenelse_eq_compute_ifthenelse], 

      (* BCVExp_Load *)
      rw [bir_cv_compute_load_eq_compute_load],

      (* BCVExp_Store *)
      rw [bir_cv_compute_store_eq_compute_store]
  
  ]
QED


(* CV translation of the computation function *)
val _  = cv_auto_trans_rec cv_n2l_def
  (WF_REL_TAC `measure (cv_size)` >> Cases_on `cv_n` >> rw [cv_size_def]);


val bir_cv_compute_exp_pre_cases  = cv_auto_trans_pre "" bir_cv_compute_exp_def;
val _ = store_thm("bir_cv_compute_exp_pre[cv_pre]", ``!v env. bir_cv_compute_exp_pre v env``,
  Induct_on `v` >>
  rw [Once bir_cv_compute_exp_pre_cases]);


val _ = export_theory ()
