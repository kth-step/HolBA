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



val _ = export_theory ()

