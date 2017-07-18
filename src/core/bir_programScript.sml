open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open wordsLib;

val _ = new_theory "bir_program";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
`;


val _ = Datatype `bir_stmt_basic_t =
  | BStmt_Declare bir_var_t
  | BStmt_Assign  bir_var_t bir_exp_t
  | BStmt_Assert  bir_exp_t
  | BStmt_Assume  bir_exp_t
`;

val _ = Datatype `bir_stmt_end_t =
  | BStmt_Jmp     bir_label_t
  | BStmt_CJmp    bir_exp_t bir_label_t bir_label_t
  | BStmt_Halt    bir_exp_t
`;

val _ = Datatype `bir_stmt_t =
  | BStmtB bir_stmt_basic_t
  | BStmtE bir_stmt_end_t
`;

val _ = Datatype `bir_block_t = <|
  bb_label          : bir_label_t ;
  bb_statements     : bir_stmt_basic_t list;
  bb_last_statement : bir_stmt_end_t |>`;

val _ = Datatype `bir_program_t = BirProgram (bir_block_t list)`;
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

val bir_stmt_ss = rewrites ((type_rws ``:bir_stmt_t``) @ (type_rws ``:bir_stmt_end_t``) @
                            (type_rws ``:bir_stmt_basic_t``));

(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_labels_of_program_def = Define `bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p`;

val bir_get_program_block_info_by_label_def = Define `bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:bir_block_t). x.bb_label = l) p
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


val bir_exec_stmtB_def = Define `
  (bir_exec_stmtB (BStmt_Declare v) st = bir_exec_stmt_declare (bir_var_name v) (bir_var_type v) st) /\
  (bir_exec_stmtB (BStmt_Assert ex) st = bir_exec_stmt_assert ex st) /\
  (bir_exec_stmtB (BStmt_Assume ex) st = bir_exec_stmt_assume ex st) /\
  (bir_exec_stmtB (BStmt_Assign v ex) st = bir_exec_stmt_assign v ex st)`;



val bir_exec_stmt_halt_def = Define `bir_exec_stmt_halt ex (st : bir_state_t) =
    (st with bst_status := BST_Halted (bir_eval_exp ex st.bst_environ))`;

val bir_exec_stmt_jmp_def = Define `bir_exec_stmt_jmp p l (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))`;

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
  (bir_exec_stmt p (BStmtB bst) st =
     let st' = bir_exec_stmtB bst st in
     if (bir_state_is_terminated st') then st' else (st' with bst_pc updated_by bir_pc_next)) /\
  (bir_exec_stmt p (BStmtE bst) st = bir_exec_stmtE p bst st)`;


val bir_exec_step_def = Define `bir_exec_step p state =
  if (bir_state_is_terminated state) then state else
  case (bir_get_current_statement p state.bst_pc) of
    | NONE => bir_state_set_failed state
    | SOME stm => (bir_exec_stmt p stm state)
`;



(* ------------------------------------------------------------------------- *)
(*  Executing multiple steps                                                 *)
(* ------------------------------------------------------------------------- *)

val bir_exec_steps_opt_def = Define `bir_exec_steps_opt p state b max_steps =
   OWHILE (\ (n, st). option_CASE max_steps T (\m. n < (m:num)) /\
                      ~(bir_state_is_terminated st)) (\ (n, st).
     (SUC n, bir_exec_step p st)) (b, state)`;

val bir_exec_step_n_def = Define `
  bir_exec_step_n p state n = THE (bir_exec_steps_opt p state 0 (SOME n))`;

val bir_exec_steps_def = Define `
  (bir_exec_steps p state = bir_exec_steps_opt p state 0 NONE)`


val bir_exec_steps_opt_NONE_REWRS = store_thm ("bir_exec_steps_opt_NONE_REWRS",
  ``bir_exec_steps_opt p state b NONE =
    (if bir_state_is_terminated state then SOME (b, state) else
       bir_exec_steps_opt p (bir_exec_step p state) (SUC b) NONE)``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bir_exec_steps_opt_def] >>
METIS_TAC[]);


val bir_exec_steps_opt_SOME_REWRS = store_thm ("bir_exec_steps_opt_SOME_REWRS",
  ``bir_exec_steps_opt p state b (SOME m) =
    (if ((m <= b) \/ bir_state_is_terminated state) then SOME (b, state) else
       bir_exec_steps_opt p (bir_exec_step p state) (SUC b) (SOME m))``,

SIMP_TAC std_ss [Once whileTheory.OWHILE_THM, bir_exec_steps_opt_def] >>
COND_CASES_TAC >> FULL_SIMP_TAC arith_ss []);


val FUNPOW_bir_exec_steps_opt_REWR = store_thm ("FUNPOW_bir_exec_steps_opt_REWR",
  ``!n p b st. (FUNPOW (\(n,st). (SUC n,bir_exec_step p st)) n (b,st)) =
      (b + n, FUNPOW (bir_exec_step p) n st)``,
Induct >> ASM_SIMP_TAC arith_ss [arithmeticTheory.FUNPOW]);


val bir_exec_steps_opt_EQ_NONE = store_thm ("bir_exec_steps_opt_EQ_NONE",
  ``(bir_exec_steps_opt p state b mo = NONE) <=>
    ((mo = NONE) /\ (!n. ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state))))``,

SIMP_TAC (std_ss ++ boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_opt_def, whileTheory.OWHILE_EQ_NONE,
  FUNPOW_bir_exec_steps_opt_REWR, FORALL_AND_THM] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `mo` >> SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `x` >> DECIDE_TAC);


val bir_exec_steps_EQ_NONE = store_thm ("bir_exec_steps_EQ_NONE",
  ``(bir_exec_steps p state = NONE) <=>
    (!n. ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_NONE]);


val bir_exec_steps_opt_EQ_SOME = store_thm ("bir_exec_steps_opt_EQ_SOME",
  ``(case mo of NONE => T | SOME m => (b <= m)) ==>
    ((bir_exec_steps_opt p state b mo = SOME (c, state')) <=>
    ((case mo of NONE => (bir_state_is_terminated state')
               | SOME m => ((c <= m) /\ ((c < m) ==> (bir_state_is_terminated state')))) /\
     (b <= c) /\
     (state' = FUNPOW (bir_exec_step p) (c - b) state) /\
     (!n. n < c-b ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))))``,

SIMP_TAC std_ss [whileTheory.OWHILE_def, bir_exec_steps_opt_def, FUNPOW_bir_exec_steps_opt_REWR] >>
STRIP_TAC >>
Q.ABBREV_TAC `P = \n. ~(case mo of NONE => T | SOME m => b + n < m) \/
  bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)` >>
Tactical.REVERSE (Cases_on `?n. P n`) >- (
  UNABBREV_ALL_TAC >>
  FULL_SIMP_TAC std_ss [FORALL_AND_THM] >>
  Cases_on `mo` >| [
    SIMP_TAC std_ss [] >> METIS_TAC[],

    rename1 `SOME m` >>
    FULL_SIMP_TAC arith_ss [] >>
    Q.PAT_X_ASSUM `!n. b + n < m` (MP_TAC o Q.SPEC `m`) >>
    SIMP_TAC arith_ss []
  ]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `$? (P:num->bool)` (fn thm => REWRITE_TAC [thm]) >- (
  UNABBREV_ALL_TAC >>
  Q.EXISTS_TAC `n` >> FULL_SIMP_TAC std_ss []
) >>
Tactical.REVERSE (Cases_on `b <= c`) >> ASM_SIMP_TAC arith_ss [] >>
Q.ABBREV_TAC `n' = c - b` >>
`c = b + n'` by (UNABBREV_ALL_TAC >> DECIDE_TAC) >>
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
STRIP_TAC >>
EQ_TAC >| [
  STRIP_TAC >>
  `!n. n < n' ==> ~(P n)` by METIS_TAC [whileTheory.LESS_LEAST] >>
  `P n'` by METIS_TAC[whileTheory.FULL_LEAST_INTRO] >>
  NTAC 2 (POP_ASSUM MP_TAC) >>
  Q.PAT_X_ASSUM `P n` (K ALL_TAC) >>
  Q.PAT_X_ASSUM `$LEAST P = _` (K ALL_TAC) >>
  Q.UNABBREV_TAC `P` >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `mo` >> SIMP_TAC arith_ss [DISJ_IMP_THM] >>
  Cases_on `b + n' <= x` >> ASM_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC arith_ss [] >>
  Cases_on `n'` >- FULL_SIMP_TAC arith_ss [] >>
  rename1 `~(b + SUC n'' <= _)` >>
  Q.EXISTS_TAC `n''` >>
  ASM_SIMP_TAC arith_ss [],


  STRIP_TAC >>
  MATCH_MP_TAC bitTheory.LEAST_THM >>
  Q.PAT_X_ASSUM `P n` (K ALL_TAC) >>
  Q.UNABBREV_TAC `P` >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `mo` >> FULL_SIMP_TAC arith_ss [] >>
  METIS_TAC[]
]);



val bir_exec_steps_EQ_SOME = store_thm ("bir_exec_steps_EQ_SOME",
  ``((bir_exec_steps p state = SOME (c, state')) <=>
    ((bir_state_is_terminated state') /\
     (state' = FUNPOW (bir_exec_step p) c state) /\
     (!n. n < c ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n state)))))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_SOME]);


val bir_exec_steps_terminated = store_thm ("bir_exec_steps_terminated",
  ``bir_state_is_terminated state ==>
    (bir_exec_steps p state = SOME (0, state))``,

SIMP_TAC std_ss [bir_exec_steps_EQ_SOME, arithmeticTheory.FUNPOW]);



val bir_exec_steps_not_terminated = store_thm ("bir_exec_steps_not_terminated",
  ``~bir_state_is_terminated state ==>
    (bir_exec_steps p state =
       let state' = (bir_exec_step p state) in
       case bir_exec_steps p state' of
         | NONE => NONE
         | SOME (c, state'') => SOME (SUC c, state''))``,

SIMP_TAC std_ss [LET_THM] >>
Cases_on `bir_exec_steps p (bir_exec_step p state)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_NONE] >>
  REPEAT STRIP_TAC >>
  Cases_on `n` >> FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW] >>
  METIS_TAC[]
) >>
rename1 `_ = SOME xx` >> Cases_on `xx` >> rename1 `_ = SOME (c, state')` >>
ASM_SIMP_TAC std_ss [pairTheory.pair_case_thm] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_SOME, arithmeticTheory.FUNPOW] >>
REPEAT STRIP_TAC >>
Cases_on `n` >> (
  FULL_SIMP_TAC arith_ss [arithmeticTheory.FUNPOW]
) >>
METIS_TAC[]);


val bir_exec_step_n_EQ_THM = store_thm ("bir_exec_step_n_EQ_THM",
  ``((bir_exec_step_n p state n = (c, state')) <=>
     ((c <= n) /\ ((c < n) ==> (bir_state_is_terminated state'))) /\
     (state' = FUNPOW (bir_exec_step p) c state) /\
     (!n'. n' < c ==> ~(bir_state_is_terminated (FUNPOW (bir_exec_step p) n' state))))``,

SIMP_TAC std_ss [bir_exec_step_n_def] >>
Cases_on `bir_exec_steps_opt p state 0 (SOME n)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_opt_EQ_NONE]
) >>
FULL_SIMP_TAC std_ss [] >>
rename1 `x = (c, state')` >>
Cases_on `x` >>
rename1 `(c0, state'') = (c, state')` >>
FULL_SIMP_TAC (std_ss) [bir_exec_steps_opt_EQ_SOME] >>
EQ_TAC >> STRIP_TAC >- (
  REPEAT (BasicProvers.VAR_EQ_TAC) >>
  ASM_SIMP_TAC std_ss []
) >>
ASM_SIMP_TAC (std_ss ++ boolSimps.CONJ_ss) [] >>
Cases_on `c < c0` >- (
  `c < n` by DECIDE_TAC >>
  METIS_TAC[]
) >>
Cases_on `c0 < c` >- (
  `c0 < n` by DECIDE_TAC >>
  METIS_TAC[]
) >>
DECIDE_TAC);



val bir_exec_step_n_combine = store_thm ("bir_exec_step_n_combine",
  ``!p state0 state1 state2 n1 n2 c1 c2.
    (bir_exec_step_n p state0 n1 = (c1, state1)) ==>
    (bir_exec_step_n p state1 n2 = (c2, state2)) ==>
    (bir_exec_step_n p state0 (n1 + n2) = (c1+c2, state2))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC arith_ss [bir_exec_step_n_EQ_THM] >>
Cases_on `c1 < n1` >- (
  `c2 = 0` by (
     Cases_on `c2` >> FULL_SIMP_TAC arith_ss [] >>
     Q.PAT_X_ASSUM `!n'. n' < SUC _ ==> _` (MP_TAC o Q.SPEC `0`) >>
     ASM_SIMP_TAC std_ss [arithmeticTheory.FUNPOW]
  ) >>
  FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW]
) >>

`c1 = n1` by DECIDE_TAC >>
FULL_SIMP_TAC std_ss [] >> REV_FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  METIS_TAC[arithmeticTheory.FUNPOW_ADD, arithmeticTheory.ADD_COMM]
) >>
rename1 `nn < n1 + c2` >>
`~(nn < n1)` by METIS_TAC[] >>
`?nn2. nn = n1 + nn2` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS, arithmeticTheory.NOT_LESS] >>
FULL_SIMP_TAC arith_ss [] >>
Q.PAT_X_ASSUM `!n'. n' < c2 ==> _` (MP_TAC o Q.SPEC `nn2`) >>
FULL_SIMP_TAC std_ss [] >>
METIS_TAC[arithmeticTheory.FUNPOW_ADD, arithmeticTheory.ADD_COMM]
);


val bir_exec_step_n_add = store_thm ("bir_exec_step_n_add",
  ``!p state0 n1 n2.
    (bir_exec_step_n p state0 (n1 + n2) =
      let (c1, state1) = bir_exec_step_n p state0 n1 in
      let (c2, state2) = bir_exec_step_n p state1 n2 in
      (c1+c2, state2))``,

REPEAT GEN_TAC >>
Cases_on `bir_exec_step_n p state0 n1` >>
rename1 `bir_exec_step_n p state0 n1 = (c1, state1)` >>
Cases_on `bir_exec_step_n p state1 n2` >>
rename1 `bir_exec_step_n p state1 n2 = (c2, state2)` >>
ASM_SIMP_TAC std_ss [LET_THM] >>
METIS_TAC[bir_exec_step_n_combine]);


val bir_exec_step_n_REWRS_0 = prove (
  ``!p state. bir_exec_step_n p state 0 = (0, state)``,
SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, arithmeticTheory.FUNPOW]);

val bir_exec_step_n_REWRS_terminated = prove (
  ``!p state n. bir_state_is_terminated state ==> (bir_exec_step_n p state n = (0, state))``,
SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, arithmeticTheory.FUNPOW]);

val bir_exec_step_n_REWRS_1 = prove (
  ``!p state. bir_exec_step_n p state 1 =
         (if (bir_state_is_terminated state) then (0, state) else
         (1, bir_exec_step p state))``,

REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated state` >> (
  ASM_SIMP_TAC arith_ss [bir_exec_step_n_EQ_THM, arithmeticTheory.FUNPOW,
    numeralTheory.numeral_funpow]
) >>
REPEAT STRIP_TAC >>
`n' = 0` by DECIDE_TAC >>
FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW]);


val bir_exec_step_n_REWRS_not_terminated = prove (
  ``!p st n. ~bir_state_is_terminated st ==>
       (bir_exec_step_n p st (SUC n) =
         (let st' = bir_exec_step p st in
          let (n', st'') = bir_exec_step_n p st' n in
          (SUC n', st'')))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`, `1`, `n`] bir_exec_step_n_add) >>
ASM_SIMP_TAC arith_ss [bir_exec_step_n_REWRS_1,
  arithmeticTheory.ADD1] >>
SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) [LET_THM]);


val bir_exec_step_n_REWRS = save_thm ("bir_exec_step_n_REWRS",
  LIST_CONJ [bir_exec_step_n_REWRS_0, bir_exec_step_n_REWRS_1,
    bir_exec_step_n_REWRS_not_terminated, bir_exec_step_n_REWRS_terminated]);


val bir_exec_step_n_COUNT_0 = store_thm ("bir_exec_step_n_COUNT_0",
  ``!p state state' c. (bir_exec_step_n p state c = (0, state')) <=>
      ((state' = state) /\ (0 < c ==> bir_state_is_terminated state)) ``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_step_n_EQ_THM, arithmeticTheory.FUNPOW]);



val bir_exec_steps_combine = store_thm ("bir_exec_steps_combine",
  ``!p state0 n1 state1 c1.
    (bir_exec_step_n p state0 n1 = (c1, state1)) ==>
    (bir_exec_steps p state0 =
       case (bir_exec_steps p state1) of
         | NONE => NONE
         | SOME (c2, state2) => SOME (c1+c2, state2))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM] >>
Cases_on `c1 < n1` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_terminated, pairTheory.pair_case_thm] >>
  FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_SOME]
) >>
`c1 = n1` by DECIDE_TAC >>
REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_exec_steps p (FUNPOW (bir_exec_step p) c1 state0)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_NONE,
    GSYM arithmeticTheory.FUNPOW_ADD] >>
  GEN_TAC >>
  METIS_TAC[arithmeticTheory.ADD_COMM, arithmeticTheory.NOT_LESS,
    arithmeticTheory.LESS_EQ_EXISTS]
) >>
rename1 `_ = SOME xx` >> Cases_on `xx` >>
rename1 `_ = SOME (c2, state2)` >>
FULL_SIMP_TAC arith_ss [pairTheory.pair_case_thm, bir_exec_steps_EQ_SOME,
   GSYM arithmeticTheory.FUNPOW_ADD] >>
FULL_SIMP_TAC std_ss [] >>
GEN_TAC >> STRIP_TAC >>
Cases_on `n < c1` >> ASM_SIMP_TAC std_ss [] >>
`?nn. n = c1 + nn` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS, arithmeticTheory.NOT_LESS] >>
FULL_SIMP_TAC arith_ss []);



val bir_exec_steps_combine_GUARD = store_thm ("bir_exec_steps_combine_GUARD",
  ``!p state0 n1 state1 c1.
    (bir_exec_step_n p state0 n1 = (c1, state1)) ==>
    (bir_exec_steps p state0 =
       (if c1 < n1 then SOME (c1, state1) else (
       case (bir_exec_steps p state1) of
         | NONE => NONE
         | SOME (c2, state2) => SOME (c1+c2, state2))))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `state0`, `n1`] bir_exec_steps_combine) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `c1 < n1` >> ASM_REWRITE_TAC[] >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_terminated, pairTheory.pair_case_thm]);




val _ = export_theory();
