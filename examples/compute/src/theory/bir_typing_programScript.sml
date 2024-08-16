(* ------------------------------------------------------------------------- *)
(*  Definition of typing relation for BIR programs and statements            *)
(* ------------------------------------------------------------------------- *)


open HolKernel Parse bossLib boolLib ;
open bir_programTheory ;
open bir_envTheory ;
open bir_typingTheory ;
open listTheory ;

val _ = new_theory "bir_typing_program" ;

(* We say that a basic statement is typed when its operands are typed *)
Definition is_stmt_basic_typed_in_env_def:
  (is_stmt_basic_typed_in_env env (BStmt_Assign var exp) = is_exp_well_typed env exp)
End

(* A label is typed when the label exists in the program or when the expression is typed *)
Definition is_label_exp_typed_in_env_def:
  (is_label_exp_typed_in_env env prog (BLE_Label l) = (MEM l (bir_labels_of_program prog))) /\
  (is_label_exp_typed_in_env env prog (BLE_Exp exp) = 
    (?ity. type_of_bir_exp env exp (BType_Imm ity)))
End

(* An end statement is typed when its labels and expressions are typed *)
Definition is_stmt_end_typed_in_env_def:
  (is_stmt_end_typed_in_env env prog (BStmt_Jmp lexp) = is_label_exp_typed_in_env env prog lexp) /\
  (is_stmt_end_typed_in_env env prog (BStmt_CJmp cexp lexp1 lexp2) =
    ((type_of_bir_exp env cexp (BType_Imm Bit1)) /\ 
    (is_label_exp_typed_in_env env prog lexp1) /\ (is_label_exp_typed_in_env env prog lexp2)))
End

Definition is_stmt_typed_in_env_def:
  (is_stmt_typed_in_env env prog (BStmtB bst) = is_stmt_basic_typed_in_env env bst) /\
  (is_stmt_typed_in_env env prog (BStmtE bst) = is_stmt_end_typed_in_env env prog bst)
End

(* A block is typed when all the statements inside are typed *)
Definition is_block_typed_in_env_def:
  is_block_typed_in_env env prog block = 
    ( (EVERY (\stmt. is_stmt_basic_typed_in_env env stmt) block.bb_statements) 
    /\ (is_stmt_end_typed_in_env env prog block.bb_last_statement))
End

(* A program is typed when all its blocks are typed *)
Definition is_prog_typed_in_env_def:
  is_prog_typed_in_env env (BirProgram blist) = 
    EVERY (\b. is_block_typed_in_env env (BirProgram blist) b) blist
End


(* ------------------------------------------ *)
(* ---------------- THEOREMS ---------------- *)
(* ------------------------------------------ *)

Theorem is_prog_typed_bir_stmts_of_program:
  !p env bst.
    is_prog_typed_in_env env p ==>
    MEM bst (bir_stmts_of_program p) ==>
    is_stmt_typed_in_env env p bst
Proof
  Cases_on `p` >>
  simp [is_prog_typed_in_env_def, is_block_typed_in_env_def] >>
  simp [bir_stmts_of_program_def, bir_stmts_of_block_def] >>
  simp [MEM_FLAT, MEM_MAP] >>
  simp [EVERY_MEM] >>
  Cases_on `bst` >>
    rw [is_stmt_typed_in_env_def] >>
    fs [MEM_MAP] >>
    METIS_TAC []
QED


Theorem is_prog_typed_get_current_statement:
  !p st bst.
    (is_prog_typed_in_env st.bst_environ p) ==>
    (bir_get_current_statement p st.bst_pc = SOME bst) ==>
    (is_stmt_typed_in_env (st.bst_environ) p bst)
Proof
  rpt STRIP_TAC >>
  `MEM bst (bir_stmts_of_program p)` 
    by METIS_TAC [MEM_bir_get_current_statement_stmts_of_program] >>
  rw [is_prog_typed_bir_stmts_of_program]
QED

val _ = export_theory () ;

