(* ------------------------------------------------------------------------- *)
(*  Example where the program computes the sum of a list in memory           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open bir_cv_basicTheory bir_cv_envTheory;
open bir_cv_programTheory;


val _ = new_theory "ex_cv_sum_list";


(* The program is something like this :
* r0 = 0 // Accumulator where we sum the list
* r1 = 0 // Index in the list
* n // Size of the list (global)
* while r1 < n
*   r0 = r0 + list[r1]
*   r1 = r1 + 1
*)

(* ------------------------------------------ *)
(* ----------------- PROGRAM ---------------- *)
(* ------------------------------------------ *)

(* r0 + list[r1] *)
Definition cv_sum_one_def:
  cv_sum_one = BCVExp_BinExp BIExp_Plus (BCVExp_Den (BVar "r0"))
    (BCVExp_Load (BCVExp_Den (BVar "MEM64")) (BCVExp_Den (BVar "r1")) BEnd_BigEndian Bit64)
End

(* Statement for r0 = r0 + list[r1] *)
Definition cv_stmt_sum_one_def:
  cv_stmt_sum_one = BCVStmt_Assign (BVar "r0") cv_sum_one
End

(* r1 + 1 *)
Definition cv_incr_r1_def:
  cv_incr_r1 = BCVExp_BinExp BIExp_Plus 
      (BCVExp_Den (BVar "r1")) (BCVExp_Const (Imm64 1w))
End

(* r1 = r1 + 1 *)
Definition cv_stmt_incr_r1_def:
  cv_stmt_incr_r1 = BCVStmt_Assign (BVar "r1") cv_incr_r1
End

(* r1 < n *)
Definition cv_condition_def:
  cv_condition = BCVExp_BinPred BIExp_LessThan (BCVExp_Den (BVar "r1")) (BCVExp_Den (BVar "n"))
End

(* Block for the condition *)
Definition cv_block_cond_def:
  cv_block_cond = BCVBlock (BL_Label "cond") [] 
  (BCVStmt_CJmp cv_condition (BCVLE_Label (BL_Label "loop")) (BCVLE_Label (BL_Label "out")))
End

(* Block for the inside of the loop *)
Definition cv_block_loop_def:
  cv_block_loop = BCVBlock (BL_Label "loop") [cv_stmt_sum_one; cv_stmt_incr_r1]
    (BCVStmt_Jmp (BCVLE_Label (BL_Label "cond")))
End

(* Complete program *)
Definition cv_sum_list_program_def:
  cv_sum_list_program = BirCVProgram [cv_block_cond; cv_block_loop]
End


(* ------------------------------------------ *)
(* ------------------ STATE ----------------- *)
(* ------------------------------------------ *)


(* Adds num k in fmap at address addr *)
Definition cv_start_mem_aux_def:
  (cv_start_mem_aux alist 0 addr k = alist) /\
  (cv_start_mem_aux alist (SUC n) addr k = cv_start_mem_aux ((addr, k)::alist) n (addr+1) (k+1))
End

(* Create a memory with a list of size n *)
Definition cv_start_mem_def:
  cv_start_mem n = BCVVal_Mem Bit64 Bit64 (cv_start_mem_aux [] n 0 1)
End

(* Start program counter *)
Definition cv_start_pc_def:
  cv_start_pc = BCVProgramCounter (BL_Label "cond") 0
End

(* Start variable environment *)
Definition cv_start_env_def:
  cv_start_env n = 
  bir_cv_env_update
    (bir_cv_env_update
      (bir_cv_env_update 
        (bir_cv_env_update bir_cv_empty_env (BVar "MEM64") (cv_start_mem n)) 
        (BVar "r0") (BCVVal_Imm (Imm64 0w)))
      (BVar "r1") (BCVVal_Imm (Imm64 0w)))
    (BVar "n") (BCVVal_Imm (Imm64 (n2w n)))
End

(* Start program state *)
Definition cv_start_state_def:
  cv_start_state n = BCVState cv_start_pc (cv_start_env n) BST_Running
End




val _ = export_theory ();
