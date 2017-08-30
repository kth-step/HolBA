open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open llistTheory wordsLib;

val _ = new_theory "bir_program";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
`;

val _ = Datatype `bir_label_exp_t =
    BLE_Label bir_label_t
  | BLE_Exp bir_exp_t
`;


val _ = Datatype `bir_stmt_basic_t =
  | BStmt_Declare bir_var_t
  | BStmt_Assign  bir_var_t bir_exp_t
  | BStmt_Assert  bir_exp_t
  | BStmt_Assume  bir_exp_t
  | BStmt_Observe bir_exp_t (bir_exp_t list) (bir_val_t list -> 'a)
`;

val _ = Datatype `bir_stmt_end_t =
  | BStmt_Jmp     bir_label_exp_t
  | BStmt_CJmp    bir_exp_t bir_label_exp_t bir_label_exp_t
  | BStmt_Halt    bir_exp_t
`;

val _ = Datatype `bir_stmt_t =
  | BStmtB ('a bir_stmt_basic_t)
  | BStmtE bir_stmt_end_t
`;

val _ = Datatype `bir_block_t = <|
  bb_label          : bir_label_t ;
  bb_statements     : ('a bir_stmt_basic_t) list;
  bb_last_statement : bir_stmt_end_t |>`;

val _ = Datatype `bir_program_t = BirProgram (('a bir_block_t) list)`;
val _ = Datatype `bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>`;

val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);

val _ = Datatype `bir_status_t =
    BST_Running                  (* BIR program is still running *)
  | BST_Failed                   (* BIR program execution failed *)
  | BST_AssumptionViolated       (* BIR program execution aborted, because assumption was violated *)
  | BST_Halted bir_val_t        (* Halt called *)
  | BST_JumpOutside bir_label_t (* Jump to unknown label *)`;

val _ = Datatype `bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t
|>`;

val bir_state_t_component_equality = DB.fetch "-" "bir_state_t_component_equality";
val bir_programcounter_t_component_equality = DB.fetch "-" "bir_programcounter_t_component_equality";
val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_status_ss = rewrites (type_rws ``:bir_status_t``);

val bir_stmt_ss = rewrites ((type_rws ``:'a bir_stmt_t``) @ (type_rws ``:bir_stmt_end_t``) @
                            (type_rws ``:'a bir_stmt_basic_t``));

(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_labels_of_program_def = Define `bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p`;

val bir_get_program_block_info_by_label_def = Define `bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:'a bir_block_t). x.bb_label = l) p
`;

val bir_get_program_block_info_by_label_THM = store_thm ("bir_get_program_block_info_by_label_THM",
  ``(!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl.
          (bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
          ((((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l) /\
             (!j'. j' < i ==> (EL j' p).bb_label <> l))))``,

SIMP_TAC list_ss [bir_get_program_block_info_by_label_def, INDEX_FIND_EQ_NONE,
  listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0]);


val bir_get_program_block_info_by_label_MEM = store_thm ("bir_get_program_block_info_by_label_MEM",
  ``!p l. MEM l (bir_labels_of_program p) <=>
          (?i bl. bir_get_program_block_info_by_label p l = SOME (i, bl))``,

Cases_on `p` >> rename1 `BirProgram p` >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_labels_of_program_def, listTheory.MEM_MAP] >>
Cases_on `bir_get_program_block_info_by_label (BirProgram p) l` >| [
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM] >>
  METIS_TAC[],

  rename1 `_ = SOME ibl` >>
  Cases_on `ibl` >>
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM, listTheory.MEM_EL,
    GSYM RIGHT_EXISTS_AND_THM] >>
  METIS_TAC[]
]);



(* ------------------------------------------------------------------------- *)
(*  Program Counter                                                          *)
(* ------------------------------------------------------------------------- *)

val bir_get_current_statement_def = Define `bir_get_current_statement p pc =
  option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE
     (\ (_, bl). if (pc.bpc_index < LENGTH bl.bb_statements) then SOME (BStmtB (EL (pc.bpc_index) bl.bb_statements)) else (if pc.bpc_index = LENGTH bl.bb_statements then SOME (BStmtE bl.bb_last_statement) else NONE))`;

val bir_pc_next_def = Define `
  bir_pc_next pc = pc with bpc_index updated_by SUC`;

val bir_block_pc_def = Define `bir_block_pc l = <| bpc_label := l; bpc_index := 0 |>`

val bir_pc_first_def = Define
  `bir_pc_first (BirProgram p) = bir_block_pc (HD p).bb_label`;


(* ------------------------------------------------------------------------- *)
(*  Program State                                                            *)
(* ------------------------------------------------------------------------- *)

val bir_state_is_terminated_def = Define `bir_state_is_terminated st =
  (st.bst_status <> BST_Running)`;

val bir_state_is_terminated_IMP = store_thm ("bir_state_is_terminated_IMP",
  ``(!st. (st.bst_status = BST_Running) ==> ~(bir_state_is_terminated st)) /\
    (!st. (st.bst_status <> BST_Running) ==> (bir_state_is_terminated st))``,
  SIMP_TAC std_ss [bir_state_is_terminated_def]);

val bir_state_is_failed_def = Define `bir_state_is_failed st =
  (st.bst_status = BST_Failed)`;

val bir_state_set_failed_def = Define `bir_state_set_failed st =
  (st with bst_status := BST_Failed)`;

val bir_state_set_failed_is_failed = store_thm ("bir_state_set_failed_is_failed",
  ``!st. bir_state_is_failed (bir_state_set_failed st)``,
SIMP_TAC (std_ss ++ bir_state_ss) [bir_state_set_failed_def, bir_state_is_failed_def]);

val bir_state_init_def = Define `bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_empty_env
  ; bst_status := BST_Running
|>`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_declare_initial_value_def = Define `
  (bir_declare_initial_value (BType_Imm _) = NONE) /\
  (bir_declare_initial_value (BType_Mem at vt) = SOME (BVal_Mem at vt (K 0)))`;

val bir_exec_stmt_declare_def = Define `bir_exec_stmt_declare v ty (st : bir_state_t) =
   if bir_env_varname_is_bound st.bst_environ v then
     bir_state_set_failed st
   else (
      case (bir_env_update v (bir_declare_initial_value ty) ty st.bst_environ) of
        | SOME env => (st with bst_environ := env)
        | NONE => (* Cannot happen, since bir_declare_initial_value returns value of correct type *)            bir_state_set_failed st)`;

val bir_exec_stmt_assign_def = Define `bir_exec_stmt_assign v ex (st : bir_state_t) =
   let env_o = bir_env_write v (bir_eval_exp ex st.bst_environ) st.bst_environ in
   case env_o of
     | SOME env => (st with bst_environ := env)
     | NONE => bir_state_set_failed st`;

val bir_exec_stmt_assert_def = Define `bir_exec_stmt_assert ex (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => st
    | SOME F => bir_state_set_failed st
    | NONE => bir_state_set_failed st`

val bir_exec_stmt_assume_def = Define `bir_exec_stmt_assume ex (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssumptionViolated)
    | NONE => bir_state_set_failed st`;


val bir_exec_stmt_observe_def = Define `bir_exec_stmt_observe ec el obf (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ec st.bst_environ)) of
    | SOME T => (SOME (obf (MAP (\e. bir_eval_exp e st.bst_environ) el)), st)
    | SOME F => (NONE, st)
    | NONE => (NONE, bir_state_set_failed st)`;

val bir_exec_stmt_observe_state_def = Define `bir_exec_stmt_observe_state ec (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ec st.bst_environ)) of
    | SOME _ => st
    | NONE => bir_state_set_failed st`;


val bir_exec_stmt_observe_state_THM = store_thm ("bir_exec_stmt_observe_state_THM",
  ``!ec el obf st. SND (bir_exec_stmt_observe ec el obf st) = bir_exec_stmt_observe_state ec st``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_stmt_observe_def, bir_exec_stmt_observe_state_def] >>
REPEAT CASE_TAC >> SIMP_TAC std_ss []);


val bir_exec_stmtB_def = Define `
  (bir_exec_stmtB (BStmt_Declare v) st = (NONE, bir_exec_stmt_declare (bir_var_name v) (bir_var_type v) st)) /\
  (bir_exec_stmtB (BStmt_Assert ex) st = (NONE, bir_exec_stmt_assert ex st)) /\
  (bir_exec_stmtB (BStmt_Assume ex) st = (NONE, bir_exec_stmt_assume ex st)) /\
  (bir_exec_stmtB (BStmt_Assign v ex) st = (NONE, bir_exec_stmt_assign v ex st)) /\
  (bir_exec_stmtB (BStmt_Observe ec el obf) st = bir_exec_stmt_observe ec el obf st)`


val bir_exec_stmtB_state_def = Define `bir_exec_stmtB_state stmt st =
  SND (bir_exec_stmtB stmt st)`;


val bir_exec_stmtB_state_REWRS = store_thm ("bir_exec_stmtB_state_REWRS",
``(!v st. (bir_exec_stmtB_state (BStmt_Declare v) st = (bir_exec_stmt_declare (bir_var_name v) (bir_var_type v) st))) /\
  (!ex st. (bir_exec_stmtB_state (BStmt_Assert ex) st = (bir_exec_stmt_assert ex st))) /\
  (!ex st. (bir_exec_stmtB_state (BStmt_Assume ex) st = (bir_exec_stmt_assume ex st))) /\
  (!v ex st. (bir_exec_stmtB_state (BStmt_Assign v ex) st = (bir_exec_stmt_assign v ex st))) /\
  (!ec el obf st. (bir_exec_stmtB_state (BStmt_Observe ec el obf) st = bir_exec_stmt_observe_state ec st))``,

SIMP_TAC std_ss [bir_exec_stmtB_state_def, bir_exec_stmtB_def, bir_exec_stmt_observe_state_THM]);


val bir_exec_stmt_halt_def = Define `bir_exec_stmt_halt ex (st : bir_state_t) =
    (st with bst_status := BST_Halted (bir_eval_exp ex st.bst_environ))`;

val bir_exec_stmt_jmp_to_label_def = Define `bir_exec_stmt_jmp_to_label p
   (l : bir_label_t) (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))`;

val bir_eval_label_exp_def = Define `
   (bir_eval_label_exp (BLE_Label l) env = SOME l) /\
   (bir_eval_label_exp (BLE_Exp e) env = case bir_eval_exp e env of
      | BVal_Imm i => SOME (BL_Address i)
      | _ => NONE
   )`;

val bir_exec_stmt_jmp_def = Define `bir_exec_stmt_jmp p le (st : bir_state_t) =
    case bir_eval_label_exp le st.bst_environ of
      | NONE => bir_state_set_failed st
      | SOME l => bir_exec_stmt_jmp_to_label p l st`;

val bir_exec_stmt_cjmp_def = Define `bir_exec_stmt_cjmp p ex l1 l2 (st : bir_state_t) =
  case (bir_dest_bool_val (bir_eval_exp ex st.bst_environ)) of
    | SOME T => bir_exec_stmt_jmp p l1 st
    | SOME F => bir_exec_stmt_jmp p l2 st
    | NONE => bir_state_set_failed st`;


val bir_exec_stmtE_def = Define `
  (bir_exec_stmtE p (BStmt_Jmp l) st = bir_exec_stmt_jmp p l st) /\
  (bir_exec_stmtE p (BStmt_CJmp e l1 l2) st = bir_exec_stmt_cjmp p e l1 l2 st) /\
  (bir_exec_stmtE p (BStmt_Halt ex) st = bir_exec_stmt_halt ex st)`;


val bir_exec_stmt_def = Define `
  (bir_exec_stmt (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st =
     let (oo, st') = bir_exec_stmtB bst st in
     if (bir_state_is_terminated st') then (oo, st') else (oo, st' with bst_pc updated_by bir_pc_next)) /\
  (bir_exec_stmt p (BStmtE bst) st = (NONE, bir_exec_stmtE p bst st))`;


val bir_exec_stmt_state_def = Define `bir_exec_stmt_state p stmt state = SND (bir_exec_stmt p stmt state)`;


val bir_exec_stmt_state_REWRS = store_thm ("bir_exec_stmt_state_REWRS",
``(!p bst st. (bir_exec_stmt_state p (BStmtB bst) st =
     let st' = bir_exec_stmtB_state bst st in
     if (bir_state_is_terminated st') then st' else (st' with bst_pc updated_by bir_pc_next))) /\
  (!p est st. (bir_exec_stmt_state p (BStmtE est) st = bir_exec_stmtE p est st))``,

SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_exec_stmt_state_def, bir_exec_stmt_def, LET_THM,
  bir_exec_stmtB_state_def] >>
REPEAT GEN_TAC >> REPEAT CASE_TAC);


val bir_exec_step_def = Define `bir_exec_step p state =
  if (bir_state_is_terminated state) then (NONE, state) else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => (NONE, bir_state_set_failed state)
    | SOME stm => (bir_exec_stmt p stm state)
`;

val bir_exec_step_state_def = Define `bir_exec_step_state p state = SND (bir_exec_step p state)`;



(* ------------------------------------------------------------------------- *)
(*  Executing multiple steps                                                 *)
(* ------------------------------------------------------------------------- *)

(* In the following, we really try to define bir_exec_steps_opt below. However,
   doing so is a bit tricky. To get there, first multiple definitions about
   observations and iterating infinitely often are needed. *)


(******************************)
(* executing infinitely often *)
(******************************)

val bir_exec_infinite_steps_fun_def = Define `
  (bir_exec_infinite_steps_fun p st n = FUNPOW (bir_exec_step_state p) n st)`;


val bir_exec_infinite_steps_fun_REWRS = store_thm ("bir_exec_infinite_steps_fun_REWRS",
``(!p st. (bir_exec_infinite_steps_fun p st 0 = st)) /\
  (!p st n. (bir_exec_infinite_steps_fun p st (SUC n) =
     (bir_exec_infinite_steps_fun p (bir_exec_step_state p st) n)))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def, arithmeticTheory.FUNPOW]);


(* After how many steps do we terminate ? *)
val bir_exec_infinite_steps_COUNT_STEPS_def = Define `
  bir_exec_infinite_steps_COUNT_STEPS p st = (OLEAST i.
     bir_state_is_terminated (bir_exec_infinite_steps_fun p st i))`;


(*************************)
(* Observations produced *)
(*************************)

val bir_exec_steps_observe_llist_def = Define `
  bir_exec_steps_observe_llist p st step_no = (
     LMAP THE (LFILTER IS_SOME (LGENLIST
        (\i. FST (bir_exec_step p (bir_exec_infinite_steps_fun p st i))) step_no)))`;


val bir_exec_steps_observe_llist_0 = store_thm ("bir_exec_steps_observe_llist_0",
 ``!p st. bir_exec_steps_observe_llist p st (SOME 0) = [||]``,

REWRITE_TAC[bir_exec_steps_observe_llist_def, LGENLIST_SOME, OPT_NUM_SUC_def] >>
SIMP_TAC std_ss [LMAP, LFILTER_THM]);


val bir_exec_steps_observe_llist_NEQ_SOME0 = store_thm ("bir_exec_steps_observe_llist_NEQ_SOME0",
 ``!p st no. (no <> SOME 0) ==> (
        bir_exec_steps_observe_llist p st no =
            (let (fe, st') = bir_exec_step p st in
             let ll' = bir_exec_steps_observe_llist p st' (OPT_NUM_PRE no) in
             (OPT_LCONS fe ll')))``,

REPEAT STRIP_TAC >>
`?fe st'. bir_exec_step p st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC bool_ss [bir_exec_steps_observe_llist_def, LGENLIST_UNFOLD_NEQ_SOME0,
  combinTheory.o_DEF, bir_exec_infinite_steps_fun_REWRS, bir_exec_step_state_def] >>
ASM_SIMP_TAC std_ss [LFILTER_THM, LET_DEF] >>
Cases_on `fe` >> ASM_SIMP_TAC list_ss [LMAP, OPT_LCONS_REWRS]);



(*************************)
(* Now full execution    *)
(*************************)

val bir_exec_steps_opt_def = Define `bir_exec_steps_opt p state max_steps =
  let step_no = OPT_NUM_MIN max_steps (bir_exec_infinite_steps_COUNT_STEPS p state) in
  let ll = bir_exec_steps_observe_llist p state step_no in
  (case step_no of
    | NONE => (ll, NONE)
    | SOME i => (ll, SOME (i, bir_exec_infinite_steps_fun p state i)))`;


val bir_exec_steps_def = Define `
  (bir_exec_steps p state = bir_exec_steps_opt p state NONE)`;


val bir_exec_step_n_def = Define `
  bir_exec_step_n p state n =
  let (ll, sto) = bir_exec_steps_opt p state (SOME n) in
  (THE (toList ll), THE sto)`;


val _ = export_theory();
