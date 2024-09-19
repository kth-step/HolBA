(* ------------------------------------------------------------------------- *)
(*  Definition of BIR programs and statements                                *)
(* ------------------------------------------------------------------------- *)


open HolKernel Parse bossLib boolLib;
open birTheory;
open bir_computeTheory bir_evalTheory;
open listTheory;


val _ = new_theory "bir_program";


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
  bb_label          : bir_label_t;
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

(* Return the program counter at the start of the block *)
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


(* ----------------------------------------------- *)
(* ------------------- COMPUTE ------------------- *)
(* ----------------------------------------------- *)


(* ----------------------------------------------- *)
(* ------------------- LABELS -------------------- *)
(* ----------------------------------------------- *)

(* Compute a label expression *)
Definition bir_compute_label_exp_def:
  (bir_compute_label_exp (BLE_Label l) env = SOME l) /\
   (bir_compute_label_exp (BLE_Exp e) env = case bir_compute_exp e env of
      | SOME (BVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )
End


(* ----------------------------------------------- *)
(* --------------- BASIC STATEMENTS -------------- *)
(* ----------------------------------------------- *)


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

(* ----------------------------------------------- *)
(* --------------- END STATEMENTS ---------------- *)
(* ----------------------------------------------- *)


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

(* ----------------------------------------------- *)
(* ----------------- STATEMENTS ------------------ *)
(* ----------------------------------------------- *)

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


(* ----------------------------------------------- *)
(* --------------------- EVAL -------------------- *)
(* ----------------------------------------------- *)

(* ----------------------------------------------- *)
(* ------------------- LABELS -------------------- *)
(* ----------------------------------------------- *)

(* Eval a label expression *)
Definition bir_eval_label_exp_def:
  (bir_eval_label_exp (BLE_Label l) env l' = (l = l')) /\
  (bir_eval_label_exp (BLE_Exp e) env (BL_Address i) = bir_eval_exp env e (BVal_Imm i)) /\
  (bir_eval_label_exp _ _ _ = F)
End



(* ----------------------------------------------- *)
(* --------------- BASIC STATEMENTS -------------- *)
(* ----------------------------------------------- *)


(* Eval a basic statement *)
Definition bir_eval_stmtB_def:
  (bir_eval_stmtB (BStmt_Assign v ex) st st' = 
    (?va. (bir_eval_exp st.bst_environ ex va) 
    /\ (st' = (st with bst_environ := (bir_env_update st.bst_environ v va)))))
End

(* ----------------------------------------------- *)
(* --------------- END STATEMENTS ---------------- *)
(* ----------------------------------------------- *)


(* Eval a Jmp statement *)
Definition bir_eval_stmt_jmp_def:
  bir_eval_stmt_jmp p le (st : bir_state_t) st' =
    (?l. bir_eval_label_exp le st.bst_environ l 
    /\ bir_jmp_to_label p l st = st')
End

(* Eval a CJmp statement *)
Definition bir_eval_stmt_cjmp_def:
  bir_eval_stmt_cjmp p ec l1 l2 (st : bir_state_t) st' =
    (if bir_eval_exp st.bst_environ ec birT then 
      bir_eval_stmt_jmp p l1 st st'
    else if bir_eval_exp st.bst_environ ec birF then
      bir_eval_stmt_jmp p l2 st st'
    else F)
End

(* Eval an end statement *)
Definition bir_eval_stmtE_def:
  (bir_eval_stmtE p (BStmt_Jmp le) st st' = bir_eval_stmt_jmp p le st st') /\
  (bir_eval_stmtE p (BStmt_CJmp e l1 l2) st st' = bir_eval_stmt_cjmp p e l1 l2 st st')
End


(* ----------------------------------------------- *)
(* ----------------- STATEMENTS ------------------ *)
(* ----------------------------------------------- *)

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
