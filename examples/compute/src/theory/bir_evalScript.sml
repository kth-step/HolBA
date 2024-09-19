(* ------------------------------------------------------------------------- *)
(*  Definition of the general evaluation relation                            *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open birTheory bir_binexpTheory bir_unaryexpTheory;
open bir_binpredTheory bir_ifthenelseTheory;
open bir_memTheory;


val _ = new_theory "bir_eval";


(* General evaluation relation of bir expressions *)
Inductive bir_eval_exp:
[~BExp_Const:]
  ( !env const. bir_eval_exp env (BExp_Const const) (BVal_Imm const) )

[~BExp_MemConst:]
  ( !env aty vty mmap. bir_eval_exp env (BExp_MemConst aty vty mmap) (BVal_Mem aty vty mmap) )

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

[~BExp_Load:]
  (!env en rty e_mem e_addr v_mem v_addr v.
    ((bir_eval_exp env e_mem v_mem) /\
      (bir_eval_exp env e_addr v_addr) /\
      (bir_eval_load v_mem v_addr en rty v))
    ==>
    (bir_eval_exp env (BExp_Load e_mem e_addr en rty) v))

[~BExp_Store:]
  (!env en e_mem e_addr e_result v_mem v_addr v_result v.
    ((bir_eval_exp env e_mem v_mem) /\
      (bir_eval_exp env e_addr v_addr) /\
      (bir_eval_exp env e_result v_result) /\
      (bir_eval_store v_mem v_addr en v_result v))
    ==>
    (bir_eval_exp env (BExp_Store e_mem e_addr en e_result) v))

End



val _ = export_theory ();
