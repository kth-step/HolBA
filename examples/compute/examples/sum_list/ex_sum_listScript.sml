(* ------------------------------------------------------------------------- *)
(*  Example whene ther program computes the sum of a list in memory          *)
(* ------------------------------------------------------------------------- *)
open HolKernel Parse bossLib boolLib ;
open bir_basicTheory bir_envTheory ;
open bir_programTheory ;
open finite_mapTheory ;


val _ = new_theory "ex_sum_list"


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
Definition sum_one_def:
  sum_one = BExp_BinExp BIExp_Plus (BExp_Den (BVar "r0"))
    (BExp_Load (BExp_Den (BVar "MEM64")) (BExp_Den (BVar "r1")) BEnd_BigEndian Bit64)
End

(* Statement for r0 = r0 + list[r1] *)
Definition stmt_sum_one_def:
  stmt_sum_one = BStmt_Assign (BVar "r0") sum_one
End

(* r1 + 1 *)
Definition incr_r1_def:
  incr_r1 = BExp_BinExp BIExp_Plus 
      (BExp_Den (BVar "r1")) (BExp_Const (Imm64 1w))
End

(* r1 = r1 + 1 *)
Definition stmt_incr_r1_def:
  stmt_incr_r1 = BStmt_Assign (BVar "r1") incr_r1
End

(* r1 < n *)
Definition condition_def:
  condition = BExp_BinPred BIExp_LessThan (BExp_Den (BVar "r1")) (BExp_Den (BVar "n"))
End

(* Block for the condition *)
Definition block_cond_def:
  block_cond = <| bb_label := BL_Label "cond" ; bb_statements := [] ;
    bb_last_statement := BStmt_CJmp condition (BLE_Label (BL_Label "loop")) (BLE_Label (BL_Label "out")) |>
End

(* Block for the inside of the loop *)
Definition block_loop_def:
  block_loop = <| bb_label := BL_Label "loop" ; bb_statements := [stmt_sum_one ; stmt_incr_r1] ;
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "cond")) |>
End

(* Complete program *)
Definition sum_list_program_def:
  sum_list_program = BirProgram [block_cond; block_loop]
End


(* ------------------------------------------ *)
(* ------------------ STATE ----------------- *)
(* ------------------------------------------ *)


(* Adds num k in fmap at address addr *)
Definition start_mem_aux_def:
  (start_mem_aux fmap 0 addr k = fmap) /\
  (start_mem_aux fmap (SUC n) addr k = start_mem_aux (fmap |+ (addr, k)) n (addr+1) (k+1))
End

(* Create a memory with a list of size n *)
Definition start_mem_def:
  start_mem n = BVal_Mem Bit64 Bit64 (start_mem_aux FEMPTY n 0 1)
End

(* Start program counter *)
Definition start_pc_def:
  start_pc = <| bpc_label := BL_Label "cond" ; bpc_index := 0 |>
End

(* Start variable environment *)
Definition start_env_def:
  start_env n = 
  bir_env_update
    (bir_env_update
      (bir_env_update 
        (bir_env_update bir_empty_env (BVar "MEM64") (start_mem n)) 
        (BVar "r0") (BVal_Imm (Imm64 0w)))
      (BVar "r1") (BVal_Imm (Imm64 0w)))
    (BVar "n") (BVal_Imm (Imm64 (n2w n)))
End

(* Start program state *)
Definition start_state_def:
  start_state n = <| bst_pc := start_pc ; bst_environ := (start_env n) ;
    bst_status := BST_Running |>
End




val _ = export_theory ()
