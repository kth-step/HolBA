open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory bir_env_oldTheory;
open bir_expTheory;
open llistTheory wordsLib;
open finite_mapTheory;

val _ = new_theory "bir_program";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
End

Datatype:
  bir_label_exp_t =
    BLE_Label bir_label_t
  | BLE_Exp bir_exp_t
End


(*
  Assign variable expression
  Assert expression
  Assume expression
  Observe observation_id condition_expression expression_list observation_function
*)
Datatype:
  bir_stmt_basic_t =
  | BStmt_Assign  bir_var_t bir_exp_t
  | BStmt_Assert  bir_exp_t
  | BStmt_Assume  bir_exp_t
  | BStmt_Observe num bir_exp_t (bir_exp_t list) (bir_val_t list -> 'a)
End

Datatype:
  bir_stmt_end_t =
  | BStmt_Jmp     bir_label_exp_t
  | BStmt_CJmp    bir_exp_t bir_label_exp_t bir_label_exp_t
  | BStmt_Halt    bir_exp_t
End

Datatype:
  bir_stmt_t =
  | BStmtB ('a bir_stmt_basic_t)
  | BStmtE bir_stmt_end_t
End

Datatype:
  bir_block_t = <|
  bb_label          : bir_label_t ;
  bb_statements     : ('a bir_stmt_basic_t) list;
  bb_last_statement : bir_stmt_end_t |>
End

Datatype:
  bir_program_t = BirProgram (('a bir_block_t) list)
End
Datatype:
  bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>
End

val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);

Datatype:
  bir_status_t =
    BST_Running                  (* BIR program is still running *)
  | BST_TypeError                (* BIR program execution encountered a type error *)
  | BST_Failed                   (* BIR program execution failed, should not happen when starting in a state where pc is available in the program to execute *)
  | BST_AssumptionViolated       (* BIR program execution aborted, because assumption was violated *)
  | BST_AssertionViolated       (* BIR program execution failed, because assertion was violated *)
  | BST_Halted bir_val_t        (* Halt called *)
  | BST_JumpOutside bir_label_t (* Jump to unknown label *)
End

Datatype:
  bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t
|>
End

val bir_state_t_component_equality = DB.fetch "-" "bir_state_t_component_equality";
val bir_programcounter_t_component_equality = DB.fetch "-" "bir_programcounter_t_component_equality";
val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_status_ss = rewrites (type_rws ``:bir_status_t``);

val bir_stmt_ss = rewrites ((type_rws ``:'a bir_stmt_t``) @ (type_rws ``:bir_stmt_end_t``) @
                            (type_rws ``:'a bir_stmt_basic_t``));

Definition bir_state_restrict_vars_def:
 bir_state_restrict_vars vs st =
  st with bst_environ updated_by (bir_env_restrict_vars vs)
End

Theorem bir_state_restrict_vars_ALT_THM:
  !vs st.
    (bir_state_restrict_vars vs st).bst_environ = bir_env_restrict_vars vs st.bst_environ /\
    (bir_state_restrict_vars vs st).bst_pc = st.bst_pc /\
    (bir_state_restrict_vars vs st).bst_status = st.bst_status
Proof
  SIMP_TAC (std_ss++bir_state_ss) [bir_state_restrict_vars_def]
QED

(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition bir_labels_of_program_def:
  bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p
End

Definition bir_get_program_block_info_by_label_def:
  bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:'a bir_block_t). x.bb_label = l) p
End

Theorem bir_get_program_block_info_by_label_THM:
  (!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl.
          (bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
          ((((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l) /\
             (!j'. j' < i ==> (EL j' p).bb_label <> l))))
Proof
SIMP_TAC list_ss [bir_get_program_block_info_by_label_def, INDEX_FIND_EQ_NONE,
  listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0]
QED


Theorem bir_get_program_block_info_by_label_MEM:
  !p l. MEM l (bir_labels_of_program p) <=>
          (?i bl. bir_get_program_block_info_by_label p l = SOME (i, bl))
Proof
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
]
QED

Definition bir_get_blocks_def:
  bir_get_blocks (BirProgram p) = p
End

Theorem bir_get_blocks_INV_thm:
!p. BirProgram (bir_get_blocks p) = p
Proof
  Cases >> rw [bir_get_blocks_def]
QED

Theorem bir_get_blocks_labels_length_thm:
!p. LENGTH (bir_labels_of_program p) = LENGTH (bir_get_blocks p)
Proof
  Cases >>
  gs [bir_labels_of_program_def, bir_get_blocks_def]
QED

Theorem bir_get_blocks_labels_EL_thm:
!p i.
  (i < LENGTH (bir_get_blocks p)) ==>
  EL i (bir_labels_of_program p) = (EL i (bir_get_blocks p)).bb_label
Proof
  Cases >>
  gs [bir_labels_of_program_def, bir_get_blocks_def, listTheory.EL_MAP]
QED



(* ------------------------------------------------------------------------- *)
(*  Program Counter                                                          *)
(* ------------------------------------------------------------------------- *)

Definition bir_get_current_statement_def:
  bir_get_current_statement p pc =
  option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE
     (\ (_, bl). if (pc.bpc_index < LENGTH bl.bb_statements) then SOME (BStmtB (EL (pc.bpc_index) bl.bb_statements)) else (if pc.bpc_index = LENGTH bl.bb_statements then SOME (BStmtE bl.bb_last_statement) else NONE))
End

Definition bir_pc_next_def:
  bir_pc_next pc = pc with bpc_index updated_by SUC
End

Definition bir_block_pc_def:
  bir_block_pc l = <| bpc_label := l; bpc_index := 0 |>
End

Theorem bir_block_pc_11:
  (bir_block_pc l1 = bir_block_pc l2) <=> (l1 = l2)
Proof
SIMP_TAC (std_ss++bir_pc_ss) [bir_block_pc_def, bir_programcounter_t_component_equality]
QED

Definition bir_pc_first_def:
  bir_pc_first (BirProgram p) = bir_block_pc (HD p).bb_label
End


(* ------------------------------------------------------------------------- *)
(*  Program State                                                            *)
(* ------------------------------------------------------------------------- *)

Definition bir_state_is_terminated_def:
  bir_state_is_terminated st =
  (st.bst_status <> BST_Running)
End

Theorem bir_state_is_terminated_IMP:
  (!st. (st.bst_status = BST_Running) ==> ~(bir_state_is_terminated st)) /\
    (!st. (st.bst_status <> BST_Running) ==> (bir_state_is_terminated st))
Proof
SIMP_TAC std_ss [bir_state_is_terminated_def]
QED

Definition bir_state_set_typeerror_def:
  bir_state_set_typeerror st =
  (st with bst_status := BST_TypeError)
End
Definition bir_state_set_failed_def:
  bir_state_set_failed st =
  (st with bst_status := BST_Failed)
End

Definition bir_state_init_def:
  bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_env_default (bir_envty_of_vs {}) (* TODO: add vars of program here *)
  ; bst_status := BST_Running
|>
End


(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

Definition bir_exec_stmt_assign_def:
  bir_exec_stmt_assign v ex (st : bir_state_t) =
   case bir_eval_exp ex st.bst_environ of
     | SOME va => (case bir_env_write v va st.bst_environ of
                     | SOME env => (st with bst_environ := env)
                     | NONE => bir_state_set_typeerror st
                  )
     | NONE => bir_state_set_typeerror st
End

Definition bir_exec_stmt_assert_def:
  bir_exec_stmt_assert ex (st : bir_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssertionViolated)
    | NONE => bir_state_set_typeerror st
End

Definition bir_exec_stmt_assume_def:
  bir_exec_stmt_assume ex (st : bir_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssumptionViolated)
    | NONE => bir_state_set_typeerror st
End


Definition bir_exec_stmt_observe_def:
  bir_exec_stmt_observe oid ec el obf (st : bir_state_t) =
  let
    vol = MAP (\e. bir_eval_exp e st.bst_environ) el;
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T =>   if EXISTS IS_NONE vol then
                    (NONE, bir_state_set_typeerror st)
                  else
                    (SOME (oid, obf (MAP THE vol)), st)
    | SOME F =>   if EXISTS IS_NONE vol then
                    (NONE, bir_state_set_typeerror st)
                  else
                    (NONE, st)
    | NONE => (NONE, bir_state_set_typeerror st)
End

Definition bir_exec_stmt_observe_state_def:
  bir_exec_stmt_observe_state ec el (st : bir_state_t) =
  let
    vol = MAP (\e. bir_eval_exp e st.bst_environ) el;
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME _ =>   if EXISTS IS_NONE vol then
                    bir_state_set_typeerror st
                  else
                    st
    | NONE => bir_state_set_typeerror st
End


Theorem bir_exec_stmt_observe_state_THM:
  !oid ec el obf st. SND (bir_exec_stmt_observe oid ec el obf st) = bir_exec_stmt_observe_state ec el st
Proof
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_stmt_observe_def, bir_exec_stmt_observe_state_def, LET_DEF] >>
REPEAT CASE_TAC >> SIMP_TAC std_ss []
QED


Definition bir_exec_stmtB_def:
  (bir_exec_stmtB (BStmt_Assert ex) st = (NONE, bir_exec_stmt_assert ex st)) /\
  (bir_exec_stmtB (BStmt_Assume ex) st = (NONE, bir_exec_stmt_assume ex st)) /\
  (bir_exec_stmtB (BStmt_Assign v ex) st = (NONE, bir_exec_stmt_assign v ex st)) /\
  (bir_exec_stmtB (BStmt_Observe oid ec el obf) st = bir_exec_stmt_observe oid ec el obf st)
End


Definition bir_exec_stmtB_state_def:
  bir_exec_stmtB_state stmt st =
  SND (bir_exec_stmtB stmt st)
End


Theorem bir_exec_stmtB_exists:
  !h st.
      ?obs' st'.
        bir_exec_stmtB h st = (obs', st')
Proof
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
QED


Theorem bir_exec_stmtB_state_REWRS:
  (!ex st. (bir_exec_stmtB_state (BStmt_Assert ex) st = (bir_exec_stmt_assert ex st))) /\
  (!ex st. (bir_exec_stmtB_state (BStmt_Assume ex) st = (bir_exec_stmt_assume ex st))) /\
  (!v ex st. (bir_exec_stmtB_state (BStmt_Assign v ex) st = (bir_exec_stmt_assign v ex st))) /\
  (!oid ec el obf st. (bir_exec_stmtB_state (BStmt_Observe oid ec el obf) st = bir_exec_stmt_observe_state ec el st))
Proof
SIMP_TAC std_ss [bir_exec_stmtB_state_def, bir_exec_stmtB_def, bir_exec_stmt_observe_state_THM]
QED


Definition bir_exec_stmt_halt_def:
  bir_exec_stmt_halt ex (st : bir_state_t) =
  case bir_eval_exp ex st.bst_environ of
    | NONE => bir_state_set_typeerror st
    | SOME v => st with bst_status := BST_Halted v
End

Definition bir_exec_stmt_jmp_to_label_def:
  bir_exec_stmt_jmp_to_label p
   (l : bir_label_t) (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))
End

Definition bir_eval_label_exp_def:
  (bir_eval_label_exp (BLE_Label l) env = SOME l) /\
   (bir_eval_label_exp (BLE_Exp e) env = case bir_eval_exp e env of
      | SOME (BVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )
End

Definition bir_exec_stmt_jmp_def:
  bir_exec_stmt_jmp p le (st : bir_state_t) =
    case bir_eval_label_exp le st.bst_environ of
      | NONE => bir_state_set_typeerror st
      | SOME l => bir_exec_stmt_jmp_to_label p l st
End

Definition bir_exec_stmt_cjmp_def:
  bir_exec_stmt_cjmp p ec l1 l2 (st : bir_state_t) =
  let
    vobc = option_CASE (bir_eval_exp ec st.bst_environ) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T => bir_exec_stmt_jmp p l1 st
    | SOME F => bir_exec_stmt_jmp p l2 st
    | NONE => bir_state_set_typeerror st
End


Definition bir_exec_stmtE_def:
  (bir_exec_stmtE p (BStmt_Jmp l) st = bir_exec_stmt_jmp p l st) /\
  (bir_exec_stmtE p (BStmt_CJmp e l1 l2) st = bir_exec_stmt_cjmp p e l1 l2 st) /\
  (bir_exec_stmtE p (BStmt_Halt ex) st = bir_exec_stmt_halt ex st)
End


Definition bir_exec_stmt_def:
  (bir_exec_stmt (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st =
     let (oo, st') = bir_exec_stmtB bst st in
     if (bir_state_is_terminated st') then (oo, st') else (oo, st' with bst_pc updated_by bir_pc_next)) /\
  (bir_exec_stmt p (BStmtE bst) st = (NONE, bir_exec_stmtE p bst st))
End


Definition bir_exec_stmt_state_def:
  bir_exec_stmt_state p stmt state = SND (bir_exec_stmt p stmt state)
End


Theorem bir_exec_stmt_state_REWRS:
  (!p bst st. (bir_exec_stmt_state p (BStmtB bst) st =
     let st' = bir_exec_stmtB_state bst st in
     if (bir_state_is_terminated st') then st' else (st' with bst_pc updated_by bir_pc_next))) /\
  (!p est st. (bir_exec_stmt_state p (BStmtE est) st = bir_exec_stmtE p est st))
Proof
SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_exec_stmt_state_def, bir_exec_stmt_def, LET_THM,
  bir_exec_stmtB_state_def] >>
REPEAT GEN_TAC >> REPEAT CASE_TAC
QED


Definition bir_exec_step_def:
  bir_exec_step p state =
  if (bir_state_is_terminated state) then (NONE, state) else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => (NONE, bir_state_set_failed state)
    | SOME stm => (bir_exec_stmt p stm state)
End

Definition bir_exec_step_state_def:
  bir_exec_step_state p state = SND (bir_exec_step p state)
End



(* ------------------------------------------------------------------------- *)
(*  Executing multiple steps                                                 *)
(* ------------------------------------------------------------------------- *)

(* In the following, we really try to define bir_exec_steps_opt below. However,
   doing so is a bit tricky. To get there, first multiple definitions about
   observations and iterating infinitely often are needed. *)


(******************************)
(* executing infinitely often *)
(******************************)

Definition bir_exec_infinite_steps_fun_def:
  (bir_exec_infinite_steps_fun p st n = FUNPOW (bir_exec_step_state p) n st)
End


Theorem bir_exec_infinite_steps_fun_REWRS:
  (!p st. (bir_exec_infinite_steps_fun p st 0 = st)) /\
  (!p st n. (bir_exec_infinite_steps_fun p st (SUC n) =
     (bir_exec_infinite_steps_fun p (bir_exec_step_state p st) n)))
Proof
SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def, arithmeticTheory.FUNPOW]
QED


Definition bir_state_COUNT_PC_def:
  bir_state_COUNT_PC (count_failing:bool, pc_cond) st =
  case st.bst_status of
    | BST_JumpOutside l => pc_cond (bir_block_pc l)
    | BST_Running => pc_cond st.bst_pc
    | _ => count_failing
End


(* How often was a PC with a certain property reached. *)
Definition bir_exec_infinite_steps_fun_COUNT_PCs_def:
  (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st 0 = 0) /\
   (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st (SUC n) =
    let r = bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p
               (bir_exec_step_state p st) n in
    if (bir_state_COUNT_PC pc_cond (bir_exec_step_state p st)) then SUC r else r)
End



(* After how many steps do we terminate ? *)
Definition bir_exec_infinite_steps_COUNT_STEPS_def:
  bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st = (OLEAST i.
     bir_state_is_terminated (bir_exec_infinite_steps_fun p st i) \/
     (max_steps_opt = SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i))
)
End


(*************************)
(* Observations produced *)
(*************************)

Definition bir_exec_steps_observe_llist_def:
  bir_exec_steps_observe_llist p st step_no = (
     LMAP THE (LFILTER IS_SOME (LGENLIST
        (\i. FST (bir_exec_step p (bir_exec_infinite_steps_fun p st i))) step_no)))
End


Theorem bir_exec_steps_observe_llist_0:
  !p st. bir_exec_steps_observe_llist p st (SOME 0) = [||]
Proof
REWRITE_TAC[bir_exec_steps_observe_llist_def, LGENLIST_SOME, OPT_NUM_SUC_def] >>
SIMP_TAC std_ss [LMAP, LFILTER_THM]
QED


Theorem bir_exec_steps_observe_llist_NEQ_SOME0:
  !p st no. (no <> SOME 0) ==> (
        bir_exec_steps_observe_llist p st no =
            (let (fe, st') = bir_exec_step p st in
             let ll' = bir_exec_steps_observe_llist p st' (OPT_NUM_PRE no) in
             (OPT_LCONS fe ll')))
Proof
REPEAT STRIP_TAC >>
`?fe st'. bir_exec_step p st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC bool_ss [bir_exec_steps_observe_llist_def, LGENLIST_UNFOLD_NEQ_SOME0,
  combinTheory.o_DEF, bir_exec_infinite_steps_fun_REWRS, bir_exec_step_state_def] >>
ASM_SIMP_TAC std_ss [LFILTER_THM, LET_DEF] >>
Cases_on `fe` >> ASM_SIMP_TAC list_ss [LMAP, OPT_LCONS_REWRS]
QED



(*************************)
(* Now full execution    *)
(*************************)

Datatype:
  bir_execution_result_t =
    (* The termination ends. "BER_Ended o_list step_count pc_count st" means
       that the execution ended after "step_count" steps in state "st". During
       execution "pc_count" pcs that satisfy the given predicate where encountered
       (counting the pc of the final state st, but not the one of the initial state).
       The list "o_list" of observations was observed during execution
       (observations are produced from the observation_id and applying the observation_function). *)
    BER_Ended   ((num # 'o) list) num num bir_state_t

    (* The execution does not terminate. Since the programs are finite, this means
       it loops. Therefore there are no step counts and no final state. However a
       potentially infinite lazy list of observations is returned. *)
  | BER_Looping ((num # 'o) llist)
End

val bir_execution_result_ss = rewrites (type_rws ``:'a bir_execution_result_t``);

Definition IS_BER_Ended_def:
  (IS_BER_Ended (BER_Ended _ _ _ _) = T) /\
   (IS_BER_Ended (BER_Looping _) = F)
End


Theorem IS_BER_Ended_EXISTS:
  !ber. IS_BER_Ended ber <=> (?ol step_count pc_count final_st.
        ber = BER_Ended ol step_count pc_count final_st)
Proof
Cases_on `ber` >> SIMP_TAC (std_ss++bir_execution_result_ss) [IS_BER_Ended_def]
QED


Definition valOf_BER_Ended_def:
  valOf_BER_Ended (BER_Ended ol step_count pc_count final_st) =
  (ol, step_count, pc_count, final_st)
End

Definition valOf_BER_Ended_steps_def:
  valOf_BER_Ended_steps (BER_Ended ol step_count pc_count final_st) =
  (ol, step_count, final_st)
End


(* Now real execution. This is a clear definition, which is not well suited for evalation
   though. More efficient versions are derived later. We compute the no of steps and
   then execute this number of steps, recomputing values multiple times. *)
Definition bir_exec_steps_GEN_def:
  bir_exec_steps_GEN pc_cond p state max_steps_opt =
  let step_no = bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p state in
  let ll = bir_exec_steps_observe_llist p state step_no in
  (case step_no of
    | NONE => BER_Looping ll
    | SOME i => BER_Ended (THE (toList ll)) i
                (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i)
                (bir_exec_infinite_steps_fun p state i))
End


(* A simple instance that just runs till termination. *)
Definition bir_exec_steps_def:
  (bir_exec_steps p state = bir_exec_steps_GEN (T, (\_. T)) p state NONE)
End

(* A simple instance that counts all steps and has a fixed no of steps given.
   We are sure it terminates, therefore, the result is converted to a tuple. *)
Definition bir_exec_step_n_def:
  bir_exec_step_n p state n =
  valOf_BER_Ended_steps (bir_exec_steps_GEN (T, (\_. T)) p state (SOME n))
End

(* We might be interested in executing a certain no of blocks. *)
Definition bir_exec_block_n_def:
  bir_exec_block_n p state n =
  valOf_BER_Ended (bir_exec_steps_GEN (F, (\pc. pc.bpc_index = 0)) p state (SOME n))
End

(* Executing till a certain set of labels is useful as well. Since we might loop
   outside this set of labels, infinite runs are possible. *)
Definition bir_exec_to_labels_n_def:
  bir_exec_to_labels_n ls p state n =
  bir_exec_steps_GEN (F, \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) p state (SOME n)
End

Definition bir_exec_to_labels_def:
  bir_exec_to_labels ls p state = bir_exec_to_labels_n ls p state 1
End

val _ = export_theory();
