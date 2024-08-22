(* ------------------------------------------------------------------------- *)
(*  Example regarding a function that increments a variable in the memory    *)
(* ------------------------------------------------------------------------- *)


open HolKernel Parse bossLib boolLib;
open bir_basicTheory;
open bir_envTheory;
open finite_mapTheory;
open bir_computeTheory;


val _ = new_theory "ex_mem_incr";

Definition mem_var_def:
  mem_var = BVar "MEM8"
End

Definition mem_addr_def:
  mem_addr w = BExp_Const (Imm64 w)
End

Definition start_mem_def:
  start_mem n1 n2 = BVal_Mem Bit64 Bit8 (FEMPTY |+ (n1, n2))
End

Definition start_env_def:
  start_env n1 n2 = bir_env_update bir_empty_env mem_var (start_mem n1 n2)
End

Definition mem_incr_exp_def:
  mem_incr_exp w = 
  BExp_Store (BExp_Den mem_var) (mem_addr w) BEnd_BigEndian
    (BExp_BinExp BIExp_Plus (BExp_Const (Imm8 1w)) 
      (BExp_Load (BExp_Den mem_var) (mem_addr w) BEnd_BigEndian Bit8))
End


val _ = export_theory ();
