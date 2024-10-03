(* ------------------------------------------------------------------------- *)
(*  Definition of BIR programs and statements                                *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open birTheory bir_programTheory;
open bir_cv_basicTheory bir_cv_envTheory;
open bir_cv_computeTheory;
open listTheory;
open optionTheory;

val _ = new_theory "bir_cv_program";


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
  bir_cv_block_t = BCVBlock bir_label_t (bir_cv_stmt_basic_t list) bir_cv_stmt_end_t
End

(* A program : a list of blocks *)
Datatype:
  bir_cv_program_t = BirCVProgram (bir_cv_block_t list)
End


(* Program counter *)
Datatype:
  bir_cv_programcounter_t = BCVProgramCounter bir_label_t num
End


Datatype:
  bir_cv_state_t = BCVState bir_cv_programcounter_t bir_cv_env_t bir_status_t
End


(* ----------------------------------------------- *)
(* ----------------- DEFINITIONS ----------------- *)
(* ----------------------------------------------- *)

(* Accessors for ex record types *)
Definition bir_cv_block_get_label_def :
  bir_cv_block_get_label (BCVBlock label _ _) = label
End

Definition bir_cv_block_get_stmts_def:
  bir_cv_block_get_stmts (BCVBlock _ stmts _) = stmts
End

Definition bir_cv_block_get_end_def:
  bir_cv_block_get_end (BCVBlock _ _ end_stmt) = end_stmt
End

Definition bir_cv_programcounter_get_label_def:
  bir_cv_programcounter_get_label (BCVProgramCounter label _) = label
End

Definition bir_cv_programcounter_get_index_def:
  bir_cv_programcounter_get_index (BCVProgramCounter _ index) = index
End

Definition bir_cv_state_get_pc_def:
  bir_cv_state_get_pc (BCVState pc _ _) = pc 
End

Definition bir_cv_state_get_environ_def:
  bir_cv_state_get_environ (BCVState _ env _) = env 
End

Definition bir_cv_state_get_status_def:
  bir_cv_state_get_status (BCVState _ _ status) = status 
End



(* Get the index and block at the given label *)
Definition bir_cv_get_program_block_info_by_label_def:
  bir_cv_get_program_block_info_by_label
  (BirCVProgram p) l = INDEX_FIND 0 (\(x:bir_cv_block_t). (bir_cv_block_get_label x) = l) p
End

(* Checks whether a state is still running *)
Definition bir_cv_state_is_terminated_def:
  bir_cv_state_is_terminated (BCVState _ _ status) =
  (status <> BST_Running)
End

(* Set the program state to Failed *)
Definition bir_cv_state_set_failed_def:
  bir_cv_state_set_failed (BCVState pc env status) =
    BCVState pc env BST_Failed
End

(* Set the program state to TypeError *)
Definition bir_cv_state_set_typeerror_def:
  bir_cv_state_set_typeerror (BCVState pc env status) =
    BCVState pc env BST_TypeError
End

(* Get the statement of a program at the given program counter *)
Definition bir_cv_get_current_statement_def:
  bir_cv_get_current_statement p pc = 
    case (bir_cv_get_program_block_info_by_label p (bir_cv_programcounter_get_label pc)) of 
      | NONE => NONE
      | SOME (_, bl) => if ((bir_cv_programcounter_get_index pc) < LENGTH (bir_cv_block_get_stmts bl)) 
                        then SOME (BCVStmtB (EL (bir_cv_programcounter_get_index pc) (bir_cv_block_get_stmts bl))) 
                        else (if (bir_cv_programcounter_get_index pc) = LENGTH (bir_cv_block_get_stmts bl) 
                              then SOME (BCVStmtE (bir_cv_block_get_end bl)) 
                              else NONE)
End

(* Get all the labels of a program *)
Definition bir_cv_labels_of_program_def:
  bir_cv_labels_of_program (BirCVProgram p) =
  MAP bir_cv_block_get_label p
End

Definition is_label_in_program_aux_def:
  (is_label_in_program_aux label ([]:bir_cv_block_t list) = F) /\
  (is_label_in_program_aux label (h::t) = 
    if label = bir_cv_block_get_label h then T else is_label_in_program_aux label t)
End

Definition is_label_in_program_def:
  is_label_in_program label (BirCVProgram p) = is_label_in_program_aux label p
End

(* Return the program counter at the start of the block *)
Definition bir_cv_block_pc_def:
  bir_cv_block_pc label = BCVProgramCounter label 0
End


(* Increment a program counter *)
Definition bir_cv_pc_next_def:
  bir_cv_pc_next (BCVProgramCounter label index) = (BCVProgramCounter label (SUC index))
End

(* Increment pc in a state if necessary *)
Definition bir_cv_state_next_def:
  bir_cv_state_next (BCVState pc env status) =
     if (bir_cv_state_is_terminated (BCVState pc env status)) then (BCVState pc env status) else
       (BCVState (bir_cv_pc_next pc) env status)
End

(* Jump to a label *)
Definition bir_cv_jmp_to_label_def:
  bir_cv_jmp_to_label prog
   (l : bir_label_t) (BCVState pc env status) =
    if is_label_in_program l prog then
      (BCVState (bir_cv_block_pc l) env status)
    else (BCVState pc env (BST_JumpOutside l))
End

(* ----------------------------------------------- *)
(* ------------------- LABELS -------------------- *)
(* ----------------------------------------------- *)

(* Compute a label expression *)
Definition bir_cv_compute_label_exp_def:
  (bir_cv_compute_label_exp (BCVLE_Label l) env = SOME l) /\
   (bir_cv_compute_label_exp (BCVLE_Exp e) env = case bir_cv_compute_exp e env of
      | SOME (BCVVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )
End


(* ----------------------------------------------- *)
(* --------------- BASIC STATEMENTS -------------- *)
(* ----------------------------------------------- *)


(* Compute an Assign statement *)
Definition bir_cv_compute_stmt_assign_def:
  bir_cv_compute_stmt_assign v ex (BCVState pc env status) =
   case bir_cv_compute_exp ex env of
     | SOME va => BCVState pc (bir_cv_env_update env v va) status
     | NONE => bir_cv_state_set_typeerror (BCVState pc env status)
End

(* Compute a basic statement *)
Definition bir_cv_compute_stmtB_def:
  (bir_cv_compute_stmtB (BCVStmt_Assign v ex) st = (bir_cv_compute_stmt_assign v ex st))
End

(* ----------------------------------------------- *)
(* --------------- END STATEMENTS ---------------- *)
(* ----------------------------------------------- *)


(* Compute a Jmp statement *)
Definition bir_cv_compute_stmt_jmp_def:
  bir_cv_compute_stmt_jmp p le (st : bir_cv_state_t) =
    case bir_cv_compute_label_exp le (bir_cv_state_get_environ st) of
      | NONE => bir_cv_state_set_typeerror st
      | SOME l => bir_cv_jmp_to_label p l st
End

(* Compute a CJmp statement *)
Definition bir_cv_compute_stmt_cjmp_def:
  bir_cv_compute_stmt_cjmp p ec l1 l2 (st : bir_cv_state_t) =
    case bir_cv_compute_exp ec (bir_cv_state_get_environ st) of 
      | NONE => bir_cv_state_set_typeerror st
      | SOME v => case bir_cv_dest_bool_val v of
        | SOME T => bir_cv_compute_stmt_jmp p l1 st
        | SOME F => bir_cv_compute_stmt_jmp p l2 st 
        | NONE => bir_cv_state_set_typeerror st
End

(* Compute an end statement *)
Definition bir_cv_compute_stmtE_def:
  (bir_cv_compute_stmtE p (BCVStmt_Jmp l) st = bir_cv_compute_stmt_jmp p l st) /\
  (bir_cv_compute_stmtE p (BCVStmt_CJmp e l1 l2) st = bir_cv_compute_stmt_cjmp p e l1 l2 st)
End

(* ----------------------------------------------- *)
(* ----------------- STATEMENTS ------------------ *)
(* ----------------------------------------------- *)

(* Execute a statement given a program and a state *)
Definition bir_cv_compute_stmt_def:
  (bir_cv_compute_stmt (p:bir_cv_program_t) (BCVStmtB (bst:bir_cv_stmt_basic_t)) st =
     let st' = bir_cv_compute_stmtB bst st in bir_cv_state_next st') /\
  (bir_cv_compute_stmt p (BCVStmtE bst) st = bir_cv_compute_stmtE p bst st)
End

(* Evaluate a step of a program *)
Definition bir_cv_compute_step_def:
  bir_cv_compute_step p state =
  if (bir_cv_state_is_terminated state) then state else
  case (bir_cv_get_current_statement p (bir_cv_state_get_pc state)) of
    | NONE => bir_cv_state_set_failed state
    | SOME stm => (bir_cv_compute_stmt p stm state)
End

(* ----------------------------------------------- *)
(* ------------------ CONVERSION ----------------- *)
(* ----------------------------------------------- *)

Definition from_cv_stmt_basic_def:
  (from_cv_stmt_basic (BCVStmt_Assign var cv_exp) = (BStmt_Assign var (from_cv_exp cv_exp)))
End

Definition from_cv_label_exp_def:
  (from_cv_label_exp (BCVLE_Label label) = BLE_Label label) /\
  (from_cv_label_exp (BCVLE_Exp cv_exp) = BLE_Exp (from_cv_exp cv_exp))
End

Definition from_cv_stmt_end_def:
    (from_cv_stmt_end (BCVStmt_Jmp cv_le) = BStmt_Jmp (from_cv_label_exp cv_le)) /\
    (from_cv_stmt_end (BCVStmt_CJmp cv_cexp cv_le1 cv_le2) = 
      BStmt_CJmp (from_cv_exp cv_cexp) (from_cv_label_exp cv_le1) (from_cv_label_exp cv_le2))
End

Definition from_cv_stmt_def:
  (from_cv_stmt (BCVStmtB cv_stmt) = BStmtB (from_cv_stmt_basic cv_stmt)) /\
  (from_cv_stmt (BCVStmtE cv_stmt) = BStmtE (from_cv_stmt_end cv_stmt))
End

Definition from_cv_stmt_option_def:
  (from_cv_stmt_option (SOME v) = SOME (from_cv_stmt v)) /\
  (from_cv_stmt_option NONE = NONE)
End

Definition from_cv_block_def:
  from_cv_block cv_block = <|
    bb_label          := bir_cv_block_get_label cv_block;
    bb_statements     := MAP from_cv_stmt_basic (bir_cv_block_get_stmts cv_block);
    bb_last_statement := (from_cv_stmt_end (bir_cv_block_get_end cv_block)) |>
End

Definition from_cv_program_def:
  from_cv_program (BirCVProgram blist) = BirProgram (MAP from_cv_block blist)
End

Definition from_cv_programcounter_def:
  from_cv_programcounter (BCVProgramCounter label index) = 
    <| bpc_label := label; bpc_index := index |>
End

Definition from_cv_state_def:
  from_cv_state cv_st = <|
  bst_pc       := from_cv_programcounter (bir_cv_state_get_pc cv_st);
  bst_environ  := (from_cv_env (bir_cv_state_get_environ cv_st));
  bst_status   := bir_cv_state_get_status cv_st |>
End


(* ----------------------------------------------- *)
(* ------------------ THEOREMS ------------------- *)
(* ----------------------------------------------- *)

(* bir_state_is_terminated *)
Theorem bir_cv_state_is_terminated_eq_state_is_terminated:
  !cv_st. (bir_cv_state_is_terminated cv_st) = 
    bir_state_is_terminated (from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_state_is_terminated_def, bir_state_is_terminated_def] >>
  rw [from_cv_state_def, bir_cv_state_get_status_def]
QED

(* Definition for theorem purposes *)
Definition from_num_cv_block_option_def:
  (from_num_cv_block_option NONE = NONE) /\
  (from_num_cv_block_option (SOME (n:num,cv_b)) = SOME (n, from_cv_block cv_b))
End

Theorem INDEX_FIND_from_cv_block:
  !n P l. INDEX_FIND n P (MAP from_cv_block l) = 
    from_num_cv_block_option (INDEX_FIND n (\x. P (from_cv_block x)) l)
Proof
  Induct_on `l` >>
  rw [INDEX_FIND_def, from_num_cv_block_option_def]
QED

(* bir_get_current_statement *)
Theorem bir_cv_get_current_statement_eq_get_current_statement:
  !cv_prog pc. from_cv_stmt_option (bir_cv_get_current_statement cv_prog pc) =
    bir_get_current_statement (from_cv_program cv_prog) (from_cv_programcounter pc)
Proof
  Cases_on `cv_prog` >> Cases_on `pc` >>
  rw [from_cv_programcounter_def] >>
  rw [bir_get_current_statement_def, bir_cv_get_current_statement_def] >>
  rw [bir_cv_programcounter_get_label_def, bir_cv_programcounter_get_index_def] >>
  rw [bir_cv_get_program_block_info_by_label_def] >>
  rw [bir_get_program_block_info_by_label_def, from_cv_program_def] >>
  rw [INDEX_FIND_from_cv_block, from_cv_block_def] >>
  CASE_TAC >> rw [from_num_cv_block_option_def, from_cv_stmt_option_def] >>
  CASE_TAC >> rw [from_num_cv_block_option_def, from_cv_stmt_option_def] >>
  fs [from_cv_stmt_def, from_cv_block_def, from_cv_stmt_basic_def, from_cv_stmt_end_def, EL_MAP]
QED

(* bir_compute_label_exp *)
Theorem bir_cv_compute_label_exp_eq_compute_label_exp:
  !cv_le cv_env.
    bir_cv_compute_label_exp cv_le cv_env = 
      bir_compute_label_exp (from_cv_label_exp cv_le) (from_cv_env cv_env)
Proof
  Cases_on `cv_le` >>
  rw [bir_cv_compute_label_exp_def, bir_compute_label_exp_def, from_cv_label_exp_def] >>
  rw [bir_compute_exp_eq_cv_compute_exp] >>
  CASE_TAC >> rw [from_cv_val_option_def] >>
  CASE_TAC >> rw [from_cv_val_def]
QED
  

Theorem bir_is_label_in_program_eq_MEM:
  !l cv_prog.
    is_label_in_program l cv_prog = 
      MEM l (bir_labels_of_program (from_cv_program cv_prog))
Proof
  Cases_on `cv_prog` >>
  rw [from_cv_program_def, bir_labels_of_program_def] >>
  rw [MEM_MAP] >>
  Induct_on `l` >>
  rw [is_label_in_program_def, is_label_in_program_aux_def] >>
  eq_tac >>
  rw [] >| [
    qexists `from_cv_block h` >> rw [from_cv_block_def] >>
    qexists `h` >> rw [],
    metis_tac [is_label_in_program_def, from_cv_block_def],
    rw [is_label_in_program_def, from_cv_block_def],
    metis_tac [is_label_in_program_def, from_cv_block_def]
  ]
QED

Theorem bir_cv_block_pc_eq_block_pc:
  !l. from_cv_programcounter (bir_cv_block_pc l) = bir_block_pc l
Proof
  rw [bir_cv_block_pc_def, bir_block_pc_def] >>
  rw [from_cv_programcounter_def]
QED

(* bir_jmp_to_label *)
Theorem bir_cv_jmp_to_label_eq_jmp_to_label:
  !cv_prog l cv_st. 
  from_cv_state (bir_cv_jmp_to_label cv_prog l cv_st) =
    bir_jmp_to_label (from_cv_program cv_prog) l (from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_jmp_to_label_def, bir_jmp_to_label_def] >>
  fs [bir_is_label_in_program_eq_MEM] >>
  rw [from_cv_state_def] >>
  rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def,
    bir_cv_state_get_status_def, bir_cv_block_pc_eq_block_pc]
QED

(* bir_compute_stmt_jmp *)
Theorem bir_cv_compute_stmt_jmp_eq_compute_stmt_jmp:
  !cv_prog cv_le cv_st.
    from_cv_state (bir_cv_compute_stmt_jmp cv_prog cv_le cv_st) =
      bir_compute_stmt_jmp (from_cv_program cv_prog) (from_cv_label_exp cv_le) (from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_compute_stmt_jmp_def, bir_compute_stmt_jmp_def] >>
  rw [bir_cv_compute_label_exp_eq_compute_label_exp] >>
  rw [SimpRHS, Once from_cv_state_def] >>
  CASE_TAC >| [
    rw [from_cv_state_def, bir_state_set_typeerror_def, bir_cv_state_set_typeerror_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def],

    rw [bir_cv_jmp_to_label_eq_jmp_to_label]
  ]
QED

(* bir_compute_stmt_cjmp *)
Theorem bir_cv_compute_stmt_cjmp_eq_compute_stmt_cjmp:
  !cv_prog cv_cexp cv_le1 cv_le2 cv_st.
    from_cv_state (bir_cv_compute_stmt_cjmp cv_prog cv_cexp cv_le1 cv_le2 cv_st) = 
    bir_compute_stmt_cjmp (from_cv_program cv_prog) (from_cv_exp cv_cexp)
        (from_cv_label_exp cv_le1) (from_cv_label_exp cv_le2)(from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_compute_stmt_cjmp_def, bir_compute_stmt_cjmp_def] >>
  CASE_TAC >| [
    rw [bir_compute_exp_eq_cv_compute_exp, from_cv_state_def] >>
    rw [from_cv_val_option_def] >>
    rw [bir_cv_state_set_typeerror_def, bir_state_set_typeerror_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def],


    rw [SimpRHS, bir_compute_exp_eq_cv_compute_exp, from_cv_state_def] >>
    rw [from_cv_val_option_def] >>
    rw [bir_cv_dest_bool_val_eq_dest_bool_val] >>
    CASE_TAC >| [
      rw [from_cv_state_def, bir_cv_state_set_typeerror_def, bir_state_set_typeerror_def] >>
      rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def],

      rw [bir_cv_compute_stmt_jmp_eq_compute_stmt_jmp] >>
      rw [from_cv_state_def]
    ]
  ]
QED

(* bir_compute_stmtE *)
Theorem bir_cv_compute_stmtE_eq_compute_stmtE:
  !cv_prog cv_stmt cv_st. from_cv_state (bir_cv_compute_stmtE cv_prog cv_stmt cv_st) =
    bir_compute_stmtE (from_cv_program cv_prog) (from_cv_stmt_end cv_stmt) (from_cv_state cv_st)
Proof
  Cases_on `cv_stmt` >>
  rw [bir_cv_compute_stmtE_def, bir_compute_stmtE_def, from_cv_stmt_end_def] >| [
    rw [bir_cv_compute_stmt_jmp_eq_compute_stmt_jmp],

    rw [bir_cv_compute_stmt_cjmp_eq_compute_stmt_cjmp]
  ]
QED

(* bir_compute_stmt_assign *)
Theorem bir_cv_compute_stmt_assign_eq_compute_stmt_assign:
  !var cv_exp cv_st . from_cv_state (bir_cv_compute_stmt_assign var cv_exp cv_st) = 
    bir_compute_stmt_assign var (from_cv_exp cv_exp) (from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_compute_stmt_assign_def, bir_compute_stmt_assign_def] >>
  rw [from_cv_state_def] >>
  rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
  rw [bir_compute_exp_eq_cv_compute_exp] >>
  CASE_TAC >> rw [from_cv_val_option_def] >| [
    rw [bir_cv_state_set_typeerror_def, bir_state_set_typeerror_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def],

    rw [bir_cv_state_set_typeerror_def, bir_state_set_typeerror_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def],

    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
    metis_tac [from_cv_env_cv_env_update],

    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
    metis_tac [from_cv_env_cv_env_update]
  ]
QED

(* bir_compute_stmtB *)
Theorem bir_cv_compute_stmtB_eq_compute_stmtB:
  !cv_stmt cv_st. from_cv_state (bir_cv_compute_stmtB cv_stmt cv_st) =
    bir_compute_stmtB (from_cv_stmt_basic cv_stmt) (from_cv_state cv_st)
Proof
  Cases_on `cv_stmt` >>
  rw [bir_cv_compute_stmtB_def, bir_compute_stmtB_def, from_cv_stmt_basic_def] >| [
    rw [bir_cv_compute_stmt_assign_eq_compute_stmt_assign]
  ]
QED

Theorem bir_cv_pc_next_eq_pc_next:
  !b. from_cv_programcounter (bir_cv_pc_next b) = bir_pc_next (from_cv_programcounter b)
Proof
  Cases_on `b` >>
  rw [from_cv_programcounter_def, bir_pc_next_def, bir_cv_pc_next_def]
QED

Theorem bir_cv_state_next_eq_state_next:
  !cv_st. from_cv_state (bir_cv_state_next cv_st) = bir_state_next (from_cv_state cv_st)
Proof
  Cases_on `cv_st` >>
  rw [bir_cv_state_next_def, bir_state_next_def] >>
  fs [from_cv_state_def, bir_cv_state_is_terminated_def, bir_state_is_terminated_def] >>
  fs [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
  rw [bir_cv_pc_next_eq_pc_next]
QED

(* bir_compute_stmt *)
Theorem bir_cv_compute_stmt_eq_compute_stmt:
  !cv_prog cv_st cv_stmt. from_cv_state (bir_cv_compute_stmt cv_prog cv_stmt cv_st) = 
    bir_compute_stmt (from_cv_program cv_prog) (from_cv_stmt cv_stmt) (from_cv_state cv_st)
Proof
  Cases_on `cv_stmt` >>
  rw [bir_cv_compute_stmt_def, bir_compute_stmt_def, from_cv_stmt_def] >| [
    rw [bir_cv_state_next_eq_state_next, bir_cv_compute_stmtB_eq_compute_stmtB],

    rw [bir_cv_compute_stmtE_eq_compute_stmtE]
  ]
QED

Theorem bir_cv_compute_step_eq_compute_exp:
  !cv_p cv_st. from_cv_state (bir_cv_compute_step cv_p cv_st) =
   bir_compute_step (from_cv_program cv_p) (from_cv_state cv_st)
Proof
  Cases_on `cv_p` >> Cases_on `cv_st` >>
  rw [bir_compute_step_def, bir_cv_compute_step_def] >>
  fs [bir_cv_state_is_terminated_eq_state_is_terminated] >>
  rw [bir_cv_state_get_pc_def] >>
  CASE_TAC >| [
    rw [from_cv_state_def, from_cv_stmt_option_def, bir_state_set_failed_def, bir_cv_state_set_failed_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
    rw [GSYM bir_cv_get_current_statement_eq_get_current_statement] >>
    rw [from_cv_state_def, from_cv_stmt_option_def, bir_state_set_failed_def, bir_cv_state_set_failed_def],

    rw [SimpRHS, Once from_cv_state_def, from_cv_stmt_option_def] >>
    rw [bir_cv_state_get_pc_def, bir_cv_state_get_environ_def, bir_cv_state_get_status_def] >>
    rw [bir_cv_compute_stmt_eq_compute_stmt] >>
    rw [GSYM bir_cv_get_current_statement_eq_get_current_statement] >>
    rw [from_cv_stmt_option_def]
  ]
QED


val _ = export_theory ()

