open HolKernel Parse bossLib boolLib
open bir_basicTheory bir_binexpTheory bir_unaryexpTheory bir_envTheory


val _ = new_theory "bir_compute"


Definition bir_compute_exp_def:
  (bir_compute_exp (BExp_Const n) env = SOME (BVal_Imm n)) /\

  (* (bir_compute (BExp_MemConst aty vty mmap) env = SOME (BVal_Mem aty vty mmap)) /\ *)

  (bir_compute_exp (BExp_Den (BVar id)) env = bir_env_lookup env id) /\

  (* (bir_compute (BExp_Cast ct e ty) env = ( *)
  (*    bir_eval_cast ct (bir_compute e env) ty)) /\ *)

  (bir_compute_exp (BExp_UnaryExp et e) env = (
     bir_compute_unaryexp et (bir_compute_exp e env))) /\

  (bir_compute_exp (BExp_BinExp et e1 e2) env = (
     bir_compute_binexp et (bir_compute_exp e1 env) (bir_compute_exp e2 env))) /\

  (bir_compute_exp (BExp_BinPred pt e1 e2) env = (
     bir_compute_binpred pt (bir_compute_exp e1 env) (bir_compute_exp e2 env)))
  (**)
  (* (bir_compute (BExp_MemEq e1 e2) env = ( *)
  (*    bir_eval_memeq (bir_compute e1 env) (bir_compute e2 env))) /\ *)
  (**)
  (**)
  (* (bir_compute (BExp_IfThenElse c et ef) env = *)
  (*    bir_eval_ifthenelse (bir_compute c env) (bir_compute et env) (bir_compute ef env) *)
  (* ) /\ *)
  (**)
  (* (bir_compute (BExp_Load mem_e a_e en ty) env = *)
  (*    bir_eval_load (bir_compute mem_e env) (bir_compute a_e env) en ty) /\ *)
  (**)
  (* (bir_compute (BExp_Store mem_e a_e en v_e) env = *)
  (*    bir_eval_store (bir_compute mem_e env) (bir_compute a_e env) en (bir_compute v_e env)) *)
End


val _ = export_theory ()
