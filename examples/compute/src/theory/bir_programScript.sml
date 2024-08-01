(* ------------------------------------------------------------------------- *)
(*  Definition of BIR programs and statements                                *)
(* ------------------------------------------------------------------------- *)


open HolKernel Parse bossLib boolLib ;
open bir_basicTheory bir_envTheory ;


val _ = new_theory "bir_program" ;


(* Label values for jumps *)
Datatype:
  bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
End

(* Label expressions that may be computed *)
Datatype:
  bir_label_exp_t =
    BLE_Label bir_label_t
  | BLE_Exp bir_exp_t
End



(* Statements inside a program block *)
Datatype:
  bir_stmt_basic_t = 
    | BStmt_Assign bir_var_t bir_exp_t
End

(* Statements at the end of a block *)
Datatype:
  bir_stmt_end_t = 
    | BStmt_Jmp bir_label_exp_t
    | BStmt_CJmp bir_exp_t bir_label_exp_t bir_label_exp_t
End

(* General statement type *)
Datatype:
  bir_stmt_t =
  | BStmtB bir_stmt_basic_t
  | BStmtE bir_stmt_end_t
End



(* Block type : a label, basic statements and an end statement *)
Datatype:
  bir_block_t = <|
  bb_label          : bir_label_t ;
  bb_statements     : bir_stmt_basic_t list;
  bb_last_statement : bir_stmt_end_t |>
End

(* A program : a list of blocks *)
Datatype:
  bir_program_t = BirProgram (bir_block_t list)
End

(* Program counter : label of the current block and the offset inside the block *)
Datatype:
  bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>
End


(* Program state *)
Datatype:
  bir_status_t =
    BST_Running                  (* BIR program is still running *)
  | BST_TypeError                (* BIR program execution encountered a type error *)
  | BST_Failed                   (* BIR program execution failed, should not happen when starting in a state where pc is available in the program to execute *)
  | BST_JumpOutside bir_label_t (* Jump to unknown label *)
End

Datatype:
  bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t
|>
End


val _ = export_theory () ;
