(* ------------------------------------------------------------------------- *)
(*  Definition of BIR programs and statements                                *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_cv_basicTheory bir_cv_envTheory ;
open bir_programTheory ;
open bir_cv_computeTheory ;

val _ = new_theory "bir_cv_program" ;


(* Label expressions that may be computed *)
Datatype:
  bir_cv_label_exp_t =
    BCVLE_Label bir_label_t
  | BCVLE_Exp bir_cv_exp_t
End



(* Statements inside a program block *)
Datatype:
  bir_cv_stmt_basic_t = 
    | BCVStmt_Assign bir_var_t bir_cv_exp_t
End

(* Statements at the end of a block *)
Datatype:
  bir_cv_stmt_end_t = 
    | BCVStmt_Jmp bir_cv_label_exp_t
    | BCVStmt_CJmp bir_cv_exp_t bir_cv_label_exp_t bir_cv_label_exp_t
End

(* General statement type *)
Datatype:
  bir_cv_stmt_t =
  | BCVStmtB bir_cv_stmt_basic_t
  | BCVStmtE bir_cv_stmt_end_t
End



(* Block type : a label, basic statements and an end statement *)
Datatype:
  bir_cv_block_t = <|
  bb_label          : bir_label_t ;
  bb_statements     : bir_cv_stmt_basic_t list;
  bb_last_statement : bir_cv_stmt_end_t |>
End

(* A program : a list of blocks *)
Datatype:
  bir_cv_program_t = BirCVProgram (bir_cv_block_t list)
End

Datatype:
  bir_cv_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_cv_env_t;
  bst_status   : bir_status_t
|>
End


(* ----------------------------------------------- *)
(* ----------------- DEFINITIONS ----------------- *)
(* ----------------------------------------------- *)


(* Get the index and block at the given label *)
Definition bir_cv_get_program_block_info_by_label_def:
  bir_cv_get_program_block_info_by_label
  (BirCVProgram p) l = INDEX_FIND 0 (\(x:bir_cv_block_t). x.bb_label = l) p
End

(* Checks whether a state is still running *)
Definition bir_cv_state_is_terminated_def:
  bir_cv_state_is_terminated st =
  (st.bst_status <> BST_Running)
End

(* Set the program state to Failed *)
Definition bir_cv_state_set_failed_def:
  bir_cv_state_set_failed st =
  (st with bst_status := BST_Failed)
End

(* Set the program state to TypeError *)
Definition bir_cv_state_set_typeerror_def:
  bir_cv_state_set_typeerror st =
  (st with bst_status := BST_TypeError)
End

(* Get the statement of a program at the given program counter *)
Definition bir_cv_get_current_statement_def:
  bir_cv_get_current_statement p pc = 
    case (bir_cv_get_program_block_info_by_label p pc.bpc_label) of 
      | NONE => NONE
      | SOME (_, bl) => if (pc.bpc_index < LENGTH bl.bb_statements) 
                        then SOME (BCVStmtB (EL (pc.bpc_index) bl.bb_statements)) 
                        else (if pc.bpc_index = LENGTH bl.bb_statements 
                              then SOME (BCVStmtE bl.bb_last_statement) 
                              else NONE)
End

(* Get all the labels of a program *)
Definition bir_cv_labels_of_program_def:
  bir_cv_labels_of_program (BirCVProgram p) =
  MAP (\bl. bl.bb_label) p
End

(* Retuern the program counter at the start of the block *)
(* Definition bir_block_pc_def: *)
(*   bir_block_pc l = <| bpc_label := l; bpc_index := 0 |> *)
(* End *)

(* Increment pc in a state if necessary *)
Definition bir_cv_state_next_def:
  bir_cv_state_next st =
     if (bir_cv_state_is_terminated st) then st else st with bst_pc updated_by bir_pc_next
End

(* Jump to a label *)
Definition bir_cv_jmp_to_label_def:
  bir_cv_jmp_to_label p
   (l : bir_label_t) (st : bir_cv_state_t) =
    if (MEM l (bir_cv_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))
End


val _ = export_theory ()

