(* ------------------------------------------------------------------------- *)
(*  Definition of BIR programs and statements                                *)
(* ------------------------------------------------------------------------- *)


open HolKernel Parse bossLib boolLib;
open birTheory;
open bir_computeTheory;
open listTheory;

val _ = new_theory "bir_program";

(* Compute a label expression *)
Definition bir_compute_label_exp_def:
  (bir_compute_label_exp (BLE_Label l) env = SOME l) /\
   (bir_compute_label_exp (BLE_Exp e) env = case bir_compute_exp e env of
      | SOME (BVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )
End

(* Compute an Assign statement *)
Definition bir_compute_stmt_assign_def:
  bir_compute_stmt_assign v ex (st : bir_state_t) =
   case bir_compute_exp ex st.bst_environ of
     | SOME va => (st with bst_environ := (bir_env_update st.bst_environ v va))
     | NONE => bir_state_set_typeerror st
End

(* Compute a basic statement *)
Definition bir_compute_stmtB_def:
  (bir_compute_stmtB (BStmt_Assign v ex) st = (bir_compute_stmt_assign v ex st))
End

(* Compute a Jmp statement *)
Definition bir_compute_stmt_jmp_def:
  bir_compute_stmt_jmp p le (st : bir_state_t) =
    case bir_compute_label_exp le st.bst_environ of
      | NONE => bir_state_set_typeerror st
      | SOME l => bir_jmp_to_label p l st
End

(* Compute a CJmp statement *)
Definition bir_compute_stmt_cjmp_def:
  bir_compute_stmt_cjmp p ec l1 l2 (st : bir_state_t) =
  let
    vobc = option_CASE (bir_compute_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T => bir_compute_stmt_jmp p l1 st
    | SOME F => bir_compute_stmt_jmp p l2 st
    | NONE => bir_state_set_typeerror st
End

(* Compute an end statement *)
Definition bir_compute_stmtE_def:
  (bir_compute_stmtE p (BStmt_Jmp l) st = bir_compute_stmt_jmp p l st) /\
  (bir_compute_stmtE p (BStmt_CJmp e l1 l2) st = bir_compute_stmt_cjmp p e l1 l2 st)
End

(* Execute a statement given a program and a state *)
Definition bir_compute_stmt_def:
  (bir_compute_stmt (p:bir_program_t) (BStmtB (bst:bir_stmt_basic_t)) st =
     let st' = bir_compute_stmtB bst st in bir_state_next st') /\
  (bir_compute_stmt p (BStmtE bst) st = bir_compute_stmtE p bst st)
End

(* Evaluate a step of a program *)
Definition bir_compute_step_def:
  bir_compute_step p state =
  if (bir_state_is_terminated state) then state else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => bir_state_set_failed state
    | SOME stm => (bir_compute_stmt p stm state)
End

Inductive bir_eval_step:
[~BStmtB:]
!p state bst.
  ((~bir_state_is_terminated state) /\
  (bir_get_current_statement p state.bst_pc = SOME (BStmtB bst)) /\
  (bir_eval_stmtB bst state state'))
  ==>
  bir_eval_step p state (bir_state_next state')

[~BStmtE:]
!p state bst.
  ((~bir_state_is_terminated state) /\
  (bir_get_current_statement p state.bst_pc = SOME (BStmtE bst)) /\
  (bir_eval_stmtE p bst state state'))
  ==>
  (bir_eval_step p state state')

[~NoStatemnt:]
!p state.
  ((~bir_state_is_terminated state) /\
  (bir_get_current_statement p state.bst_pc = NONE))
  ==>
  (bir_eval_step p state (bir_state_set_failed state))
End

(* ----------------------------------------------- *)
(* ------------------ THEOREMS ------------------- *)
(* ----------------------------------------------- *)

Theorem MEM_INDEX_FIND_SOME:
  !n l P i e.
    INDEX_FIND n P l = SOME (i,e) ==>
    MEM e l
Proof
  Induct_on `l` >> rw [INDEX_FIND_def] >> metis_tac []
QED

Theorem MEM_bir_get_program_block_info_by_label:
  !blist l i b. 
    bir_get_program_block_info_by_label (BirProgram blist) l = SOME (i,b) ==>
    MEM b blist
Proof
  metis_tac [bir_get_program_block_info_by_label_def, MEM_INDEX_FIND_SOME]
QED

Theorem MEM_bir_get_current_statement_stmts_of_program:
  !p pc bst.
    bir_get_current_statement p pc = SOME bst ==>
      MEM bst (bir_stmts_of_program p)
Proof
  rw [bir_get_current_statement_def] >>
  Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >>
  fs [] >>
    Cases_on `x` >> Cases_on `p` >> fs [] >>
    rw [bir_stmts_of_program_def] >>
    rw [MEM_FLAT, MEM_MAP] >>
    qexists `bir_stmts_of_block r` >> rw [] >| [
      qexists `r` >> metis_tac [MEM_bir_get_program_block_info_by_label], 
      Cases_on `pc.bpc_index < LENGTH r.bb_statements` >> 
      fs [bir_stmts_of_block_def] >>
        metis_tac [MEM_MAP, MEM_EL] 
    ]
QED

val _ = export_theory ();
