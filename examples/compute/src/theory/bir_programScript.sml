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


(* ----------------------------------------------- *)
(* ----------------- DEFINITIONS ----------------- *)
(* ----------------------------------------------- *)


(* Increment a program counter *)
Definition bir_pc_next_def:
  bir_pc_next pc = pc with bpc_index updated_by SUC
End

(* Get the index and block at the given label *)
Definition bir_get_program_block_info_by_label_def:
  bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:bir_block_t). x.bb_label = l) p
End

(* Checks whether a state is still running *)
Definition bir_state_is_terminated_def:
  bir_state_is_terminated st =
  (st.bst_status <> BST_Running)
End

(* Set the program state to Failed *)
Definition bir_state_set_failed_def:
  bir_state_set_failed st =
  (st with bst_status := BST_Failed)
End

(* Set the program state to TypeError *)
Definition bir_state_set_typeerror_def:
  bir_state_set_typeerror st =
  (st with bst_status := BST_TypeError)
End

(* Get the statement of a program at the given program counter *)
Definition bir_get_current_statement_def:
  bir_get_current_statement p pc = 
    case (bir_get_program_block_info_by_label p pc.bpc_label) of 
      | NONE => NONE
      | SOME (_, bl) => if (pc.bpc_index < LENGTH bl.bb_statements) 
                        then SOME (BStmtB (EL (pc.bpc_index) bl.bb_statements)) 
                        else (if pc.bpc_index = LENGTH bl.bb_statements 
                              then SOME (BStmtE bl.bb_last_statement) 
                              else NONE)
End

(* Get all the labels of a program *)
Definition bir_labels_of_program_def:
  bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p
End

Definition bir_stmts_of_block_def:
  bir_stmts_of_block b = 
    (BStmtE b.bb_last_statement) :: MAP (\bst. (BStmtB bst)) b.bb_statements
End

Definition bir_stmts_of_program_def:
  bir_stmts_of_program (BirProgram blist) = 
  FLAT (MAP (\bl. bir_stmts_of_block bl) blist)
End

(* Retuern the program counter at the start of the block *)
Definition bir_block_pc_def:
  bir_block_pc l = <| bpc_label := l; bpc_index := 0 |>
End

(* Increment pc in a state if necessary *)
Definition bir_state_next_def:
  bir_state_next st =
     if (bir_state_is_terminated st) then st else st with bst_pc updated_by bir_pc_next
End

(* Jump to a label *)
Definition bir_jmp_to_label_def:
  bir_jmp_to_label p
   (l : bir_label_t) (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))
End


val _ = export_theory () ;
