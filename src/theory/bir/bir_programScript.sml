open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_expTheory;
open llistTheory wordsLib;
open finite_mapTheory;

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
  | BST_TypeError                (* BIR program execution encountered a type error *)
  | BST_Failed                   (* BIR program execution failed, should not happen when starting in a state where pc is available in the program to execute *)
  | BST_AssumptionViolated       (* BIR program execution aborted, because assumption was violated *)
  | BST_AssertionViolated       (* BIR program execution failed, because assertion was violated *)
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

val bir_block_pc_11 = store_thm ("bir_block_pc_11",
``(bir_block_pc l1 = bir_block_pc l2) <=> (l1 = l2)``,
SIMP_TAC (std_ss++bir_pc_ss) [bir_block_pc_def, bir_programcounter_t_component_equality]);

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

val bir_state_set_typeerror_def = Define `bir_state_set_typeerror st =
  (st with bst_status := BST_TypeError)`;
val bir_state_set_failed_def = Define `bir_state_set_failed st =
  (st with bst_status := BST_Failed)`;

val bir_state_init_def = Define `bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_env_default (bir_envty_of_vs {}) (* TODO: add vars of program here *)
  ; bst_status := BST_Running
|>`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmt_assign_def = Define `bir_exec_stmt_assign v ex (st : bir_state_t) =
   case bir_eval_exp ex st.bst_environ of
     | SOME va => (case bir_env_write v va st.bst_environ of
                     | SOME env => (st with bst_environ := env)
                     | NONE => bir_state_set_typeerror st
                  )
     | NONE => bir_state_set_typeerror st`;

val bir_exec_stmt_assert_def = Define `bir_exec_stmt_assert ex (st : bir_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssertionViolated)
    | NONE => bir_state_set_typeerror st`

val bir_exec_stmt_assume_def = Define `bir_exec_stmt_assume ex (st : bir_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssumptionViolated)
    | NONE => bir_state_set_typeerror st`;


val bir_exec_stmt_observe_def = Define `bir_exec_stmt_observe ec el obf (st : bir_state_t) =
  let
    vol = MAP (\e. bir_eval_exp e st.bst_environ) el;
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T =>   if EXISTS IS_NONE vol then
                    (NONE, bir_state_set_typeerror st)
                  else
                    (SOME (obf (MAP THE vol)), st)
    | SOME F =>   if EXISTS IS_NONE vol then
                    (NONE, bir_state_set_typeerror st)
                  else
                    (NONE, st)
    | NONE => (NONE, bir_state_set_typeerror st)`;

val bir_exec_stmt_observe_state_def = Define `bir_exec_stmt_observe_state ec el (st : bir_state_t) =
  let
    vol = MAP (\e. bir_eval_exp e st.bst_environ) el;
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME _ =>   if EXISTS IS_NONE vol then
                    bir_state_set_typeerror st
                  else
                    st
    | NONE => bir_state_set_typeerror st`;


val bir_exec_stmt_observe_state_THM = store_thm ("bir_exec_stmt_observe_state_THM",
  ``!ec el obf st. SND (bir_exec_stmt_observe ec el obf st) = bir_exec_stmt_observe_state ec el st``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_stmt_observe_def, bir_exec_stmt_observe_state_def, LET_DEF] >>
REPEAT CASE_TAC >> SIMP_TAC std_ss []);


val bir_exec_stmtB_def = Define `
  (bir_exec_stmtB (BStmt_Assert ex) st = (NONE, bir_exec_stmt_assert ex st)) /\
  (bir_exec_stmtB (BStmt_Assume ex) st = (NONE, bir_exec_stmt_assume ex st)) /\
  (bir_exec_stmtB (BStmt_Assign v ex) st = (NONE, bir_exec_stmt_assign v ex st)) /\
  (bir_exec_stmtB (BStmt_Observe ec el obf) st = bir_exec_stmt_observe ec el obf st)`


val bir_exec_stmtB_state_def = Define `bir_exec_stmtB_state stmt st =
  SND (bir_exec_stmtB stmt st)`;


val bir_exec_stmtB_exists =
  store_thm("bir_exec_stmtB_exists",
  ``!h st.
      ?obs' st'.
        bir_exec_stmtB h st = (obs', st')``,

Cases_on `h` >> (
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def]
) >>
FULL_SIMP_TAC std_ss [bir_exec_stmt_observe_def] >>
Cases_on `option_CASE (bir_eval_exp b st.bst_environ) NONE bir_dest_bool_val` >| [
  FULL_SIMP_TAC std_ss [LET_DEF],

  Cases_on `x` >> (
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    Cases_on `EXISTS IS_NONE (MAP (λe. bir_eval_exp e st.bst_environ) l)` >> (
      FULL_SIMP_TAC std_ss []
    )
  )
]
);


val bir_exec_stmtB_state_REWRS = store_thm ("bir_exec_stmtB_state_REWRS",
``(!ex st. (bir_exec_stmtB_state (BStmt_Assert ex) st = (bir_exec_stmt_assert ex st))) /\
  (!ex st. (bir_exec_stmtB_state (BStmt_Assume ex) st = (bir_exec_stmt_assume ex st))) /\
  (!v ex st. (bir_exec_stmtB_state (BStmt_Assign v ex) st = (bir_exec_stmt_assign v ex st))) /\
  (!ec el obf st. (bir_exec_stmtB_state (BStmt_Observe ec el obf) st = bir_exec_stmt_observe_state ec el st))``,

SIMP_TAC std_ss [bir_exec_stmtB_state_def, bir_exec_stmtB_def, bir_exec_stmt_observe_state_THM]);


val bir_exec_stmt_halt_def = Define `bir_exec_stmt_halt ex (st : bir_state_t) =
  case bir_eval_exp ex st.bst_environ of
    | NONE => bir_state_set_typeerror st
    | SOME v => st with bst_status := BST_Halted v`;

val bir_exec_stmt_jmp_to_label_def = Define `bir_exec_stmt_jmp_to_label p
   (l : bir_label_t) (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))`;

val bir_eval_label_exp_def = Define `
   (bir_eval_label_exp (BLE_Label l) env = SOME l) /\
   (bir_eval_label_exp (BLE_Exp e) env = case bir_eval_exp e env of
      | SOME (BVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )`;

val bir_exec_stmt_jmp_def = Define `bir_exec_stmt_jmp p le (st : bir_state_t) =
    case bir_eval_label_exp le st.bst_environ of
      | NONE => bir_state_set_typeerror st
      | SOME l => bir_exec_stmt_jmp_to_label p l st`;

val bir_exec_stmt_cjmp_def = Define `bir_exec_stmt_cjmp p ec l1 l2 (st : bir_state_t) =
  let
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T => bir_exec_stmt_jmp p l1 st
    | SOME F => bir_exec_stmt_jmp p l2 st
    | NONE => bir_state_set_typeerror st`;


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


val bir_state_COUNT_PC_ENV_def = Define `
  bir_state_COUNT_PC_ENV (count_failing:bool, pc_env_cond) st =
    case st.bst_status of
      | BST_JumpOutside l => (pc_env_cond (bir_block_pc l) st.bst_environ)
      | BST_Running => (pc_env_cond st.bst_pc st.bst_environ)
      | _ => count_failing
`;

(* How often a state obeying st_cond was reached. *)
val bir_exec_infinite_steps_fun_COUNT_PC_ENVs_def = Define
  `(bir_exec_infinite_steps_fun_COUNT_PC_ENVs pc_env_cond p st 0 = 0) /\
   (bir_exec_infinite_steps_fun_COUNT_PC_ENVs pc_env_cond p st (SUC n) =
    let r = bir_exec_infinite_steps_fun_COUNT_PC_ENVs pc_env_cond p
               (bir_exec_step_state p st) n in
    if (bir_state_COUNT_PC_ENV pc_env_cond (bir_exec_step_state p st)) then SUC r else r)`

(* After how many steps do we terminate ? *)
val bir_exec_infinite_steps_COUNT_STEPS_def = Define `
  bir_exec_infinite_steps_COUNT_STEPS pc_env_cond max_COUNT_PC_ENV_opt p st =
    (OLEAST i.
      bir_state_is_terminated (bir_exec_infinite_steps_fun p st i) \/
      (max_COUNT_PC_ENV_opt = SOME (bir_exec_infinite_steps_fun_COUNT_PC_ENVs pc_env_cond p st i))
    )
`;


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

(* TODO: Add "env_count" to BER_Ended *)
val _ = Datatype `bir_execution_result_t =
    (* The termination ends. "BER_Ended o_list step_count pc_count st" means
       that the execution ended after "step_count" steps in state "st". During
       execution "pc_count" states that satisfy the given Pc_cond were encountered
       (possibly including the final state st, but never the initial state).
       The list "o_list" of observations was observed during execution *)
    BER_Ended   ('o list) num num bir_state_t

    (* The execution does not terminate. Since the programs are finite, this means
       it loops. Therefore there are no step counts and no final state. However, a
       potentially infinite lazy list of observations is returned. *)
  | BER_Looping ('o llist)
`;

val bir_execution_result_ss = rewrites (type_rws ``:'a bir_execution_result_t``);

val IS_BER_Ended_def = Define `
   (IS_BER_Ended (BER_Ended _ _ _ _) = T) /\
   (IS_BER_Ended (BER_Looping _) = F)`;


val IS_BER_Ended_EXISTS = store_thm ("IS_BER_Ended_EXISTS",
``!ber. IS_BER_Ended ber <=> (?ol step_count pc_count final_st.
        ber = BER_Ended ol step_count pc_count final_st)``,

Cases_on `ber` >> SIMP_TAC (std_ss++bir_execution_result_ss) [IS_BER_Ended_def]);


val valOf_BER_Ended_def = Define `valOf_BER_Ended (BER_Ended ol step_count pc_count final_st) =
  (ol, step_count, pc_count, final_st)`;

val valOf_BER_Ended_steps_def = Define `valOf_BER_Ended_steps (BER_Ended ol step_count pc_count final_st) =
  (ol, step_count, final_st)`;


(* Now real execution. This is a clear definition, which is not well suited for evalation
   though. More efficient versions are derived later. We compute the number of steps and
   then execute this number of steps, recomputing values multiple times. *)
val bir_exec_steps_GEN_def = Define `
  bir_exec_steps_GEN pc_env_cond p state max_COUNT_PC_ENV_opt =
    let step_no = bir_exec_infinite_steps_COUNT_STEPS pc_env_cond max_COUNT_PC_ENV_opt p state in
    let ll = bir_exec_steps_observe_llist p state step_no in
    (case step_no of
      | NONE => BER_Looping ll
      | SOME i => BER_Ended (THE (toList ll)) i
		  (bir_exec_infinite_steps_fun_COUNT_PC_ENVs pc_env_cond p state i)
		  (bir_exec_infinite_steps_fun p state i))
`;


(* A simple instance that just runs till termination. *)
val bir_exec_steps_def = Define `
  (bir_exec_steps p state = bir_exec_steps_GEN (T, \_ _. T) p state NONE)`;

(* A simple instance that counts all steps and has a fixed no of steps given.
   We are sure it terminates, therefore, the result is converted to a tuple. *)
val bir_exec_step_n_def = Define `
  bir_exec_step_n p state n =
  valOf_BER_Ended_steps (bir_exec_steps_GEN (T, \_ _. T) p state (SOME n))`

(* Executes until either one block has been executed, or until env invariant has been violated. *)
val bir_exec_step_invar_def = Define `
  bir_exec_step_invar p state invar =
    valOf_BER_Ended_steps (bir_exec_steps_GEN (F, \pc env. (pc.bpc_index = 0) \/ ~(invar env)) p state (SOME 1))`

(* We might be interested in executing a certain number of blocks. *)
val bir_exec_block_n_def = Define `
  bir_exec_block_n p state n =
  valOf_BER_Ended (bir_exec_steps_GEN (F, \pc _. pc.bpc_index = 0) p state (SOME n))`

(* Executing till a certain set of labels is useful as well. Since we might loop
   outside this set of labels, infinite runs are possible. *)
val bir_exec_to_labels_n_def = Define `
  bir_exec_to_labels_n ls p state n =
  bir_exec_steps_GEN (F, (\pc _. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls))) p state (SOME n)`

val bir_exec_to_labels_def = Define `
  bir_exec_to_labels ls p state = bir_exec_to_labels_n ls p state 1`

(* To-label-execution with concurrent invariant (safe for threaded machines
 * where instructions evaluate 1 at a time): *)

(* This checks whether the invariant is violated in a state resulting from
 * execution of one block *)
val bir_is_invar_block_viol_def = Define `
  bir_is_invar_block_viol p invar pc (env:bir_var_environment_t) =
    let st = <| bst_pc := pc; bst_environ := env; bst_status := BST_Running |> in
    ~(invar (SND (SND (SND (bir_exec_block_n p st 1)))).bst_environ)
`;

val bir_exec_to_labels_block_invar_n_def = Define `
  bir_exec_to_labels_block_invar_n ls invar p state n =
    bir_exec_steps_GEN (F, (\pc env. (bir_is_invar_block_viol p invar pc env) \/ ((pc.bpc_index = 0) /\ (pc.bpc_label IN ls)))) p state (SOME n)`

val bir_exec_to_labels_block_invar_def = Define `
  bir_exec_to_labels_block_invar ls invar p state =
    bir_exec_to_labels_block_invar_n ls invar p state 1`

(* TODO: Place this where appropriate *)
val bir_exec_to_labels_block_invar_T = store_thm ("bir_exec_to_labels_block_invar_T",
 ``!ls p state.
   (bir_exec_to_labels_block_invar ls (\_. T) p state) =
     (bir_exec_to_labels ls p state)``,

FULL_SIMP_TAC std_ss [bir_exec_to_labels_block_invar_def, bir_exec_to_labels_block_invar_n_def, bir_exec_to_labels_def,
                      bir_exec_to_labels_n_def, bir_is_invar_block_viol_def, LET_DEF]
);

(* TODO *)
(* To-label-execution with parallel invariant (safe for threaded machines
 * where instructions evaluate simultaneuously): *)

(* This checks whether invariant was violated anywhere inside of a block *)
val bir_is_invar_stmt_viol_def = Define `
  bir_is_invar_stmt_viol p invar pc env =
    let st = <| bst_pc := pc; bst_environ  := env; bst_status := BST_Running |> in
    (FST (SND (bir_exec_step_invar p st invar)) <> FST (SND (bir_exec_block_n p st 1)))
`;

val bir_exec_to_labels_stmt_invar_def = Define `
  bir_exec_to_labels_stmt_invar ls invar p state =
    bir_exec_steps_GEN (F, (\pc env. (bir_is_invar_stmt_viol p invar pc env) \/ ((pc.bpc_index = 0) /\ (pc.bpc_label IN ls)))) p state (SOME 1)`

(* TODO: Place this where we have results that allow us to prove it *)
(*
val bir_exec_to_labels_stmt_invar_T = store_thm ("bir_exec_to_labels_stmt_invar_T",
 ``!ls p state.
   (bir_exec_to_labels_stmt_invar ls (\_. T) p state) =
     (bir_exec_to_labels ls p state)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_stmt_invar_def, bir_exec_to_labels_def,
                      bir_exec_to_labels_n_def, bir_is_invar_stmt_viol_def] >>
(* Needs lemmata on general execution... *)
subgoal `!p st.
         FST (SND (bir_exec_step_invar p st (\_. T))) =
           FST (SND (bir_exec_block_n p st 1))` >- (
  cheat
) >>
FULL_SIMP_TAC std_ss [LET_DEF]
);
*)

val _ = export_theory();
