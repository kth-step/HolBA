open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory
open bir_programTheory bir_program_valid_stateTheory HolBACoreSimps;
open bir_program_blocksTheory bir_program_multistep_propsTheory;

val _ = new_theory "bir_program_no_observe";


(* ------------------------------------------------------------------------- *)
(* The only statements that produce observations are observe statements      *)
(* This is exploited in this theory to have slightly simpler semantics and   *)
(* nice rewrites                                                             *)
(* ------------------------------------------------------------------------- *)


(***************************************************************)
(* Checkers for observe statements                             *)
(***************************************************************)

val bir_stmtB_is_observe_def = Define `
  (bir_stmtB_is_observe (BStmt_Observe _ _ _ _) = T) /\
  (bir_stmtB_is_observe _ = F)`;

val bir_stmtB_is_observe_ALT_DEF = store_thm ("bir_stmtB_is_observe_ALT_DEF",
  ``bir_stmtB_is_observe stmt <=> (?oid ec el obf. stmt = BStmt_Observe oid ec el obf)``,
Cases_on `stmt` >> SIMP_TAC (std_ss++holBACore_ss) [bir_stmtB_is_observe_def]);

val bir_stmt_is_observe_def = Define `
  (bir_stmt_is_observe (BStmtB stmt) = bir_stmtB_is_observe stmt) /\
  (bir_stmt_is_observe _ = F)`;

val bir_block_contains_observe_def = Define `bir_block_contains_observe bl <=>
  EXISTS bir_stmtB_is_observe bl.bb_statements`;

val bir_program_contains_observe_def = Define `bir_program_contains_observe (BirProgram p) <=>
  EXISTS bir_block_contains_observe p`;


(***************************************************************)
(* Only observe produces observations                          *)
(***************************************************************)

val bir_exec_stmtB_only_observe_produces_observation = store_thm ("bir_exec_stmtB_only_observe_produces_observation",

  ``!stmt st. IS_SOME (FST (bir_exec_stmtB stmt st)) ==> bir_stmtB_is_observe stmt``,
Cases >> SIMP_TAC std_ss [bir_exec_stmtB_def, bir_stmtB_is_observe_def]);


val bir_exec_stmt_only_observe_produces_observation = store_thm ("bir_exec_stmt_only_observe_produces_observation",
  ``!stmt p st. IS_SOME (FST (bir_exec_stmt p stmt st)) ==> bir_stmt_is_observe stmt``,
Cases >> SIMP_TAC std_ss [bir_exec_stmt_def] >>
rename1 `BStmtB stmt` >>
REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`stmt`, `st`] bir_exec_stmtB_only_observe_produces_observation) >>
`?oo st'. bir_exec_stmtB stmt st = (oo, st')` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [LET_THM, bir_stmt_is_observe_def]);


(***************************************************************)
(* This allows some rewrites                                   *)
(***************************************************************)

val bir_exec_stmtB_NO_OBSERVE = store_thm ("bir_exec_stmtB_NO_OBSERVE",
``!stmt st. ~(bir_stmtB_is_observe stmt) ==>
    (bir_exec_stmtB stmt st = (NONE, bir_exec_stmtB_state stmt st))``,

REPEAT STRIP_TAC >>
`~(IS_SOME (FST (bir_exec_stmtB stmt st)))` by
  METIS_TAC[bir_exec_stmtB_only_observe_produces_observation] >>
Cases_on `bir_exec_stmtB stmt st` >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def]);


val bir_exec_stmt_NO_OBSERVE = store_thm ("bir_exec_stmt_NO_OBSERVE",
``!stmt p st. ~(bir_stmt_is_observe stmt) ==>
    (bir_exec_stmt p stmt st = (NONE, bir_exec_stmt_state p stmt st))``,

REPEAT STRIP_TAC >>
`~(IS_SOME (FST (bir_exec_stmt p stmt st)))` by
  METIS_TAC[bir_exec_stmt_only_observe_produces_observation] >>
Cases_on `bir_exec_stmt p stmt st` >>
FULL_SIMP_TAC std_ss [bir_exec_stmt_state_def]);


val bir_exec_step_NO_OBSERVE_current = store_thm ("bir_exec_step_NO_OBSERVE_current",
``!p st. (!stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) ==>
                 ~(bir_stmt_is_observe stmt)) ==>
    (bir_exec_step p st = (NONE, bir_exec_step_state p st))``,

REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_def, bir_exec_step_state_def] >>
DISJ2_TAC >>
Cases_on `bir_get_current_statement p st.bst_pc` >> FULL_SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [GSYM bir_exec_stmt_state_def, bir_exec_stmt_NO_OBSERVE]);


val bir_exec_step_NO_OBSERVE = store_thm ("bir_exec_step_NO_OBSERVE",
``!p st. (~(bir_program_contains_observe p)) ==>
    (bir_exec_step p st = (NONE, bir_exec_step_state p st))``,

Cases >> rename1 `BirProgram p` >>
REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_exec_step_NO_OBSERVE_current >>
Cases >> SIMP_TAC std_ss [bir_stmt_is_observe_def] >>
SIMP_TAC std_ss [bir_get_current_statement_SOME_B] >>
STRIP_TAC >>
rename1 `stmt = EL _ _` >>
FULL_SIMP_TAC list_ss [bir_get_program_block_info_by_label_THM,
  bir_program_contains_observe_def, combinTheory.o_DEF,
  listTheory.EVERY_MEM, bir_block_contains_observe_def] >>
METIS_TAC[listTheory.MEM_EL]);


val bir_exec_steps_observe_llist_NO_OBSERVE = store_thm ("bir_exec_steps_observe_llist_NO_OBSERVE",
``!p st step_no. (~(bir_program_contains_observe p)) ==>
     (bir_exec_steps_observe_llist p st step_no = [||])``,

SIMP_TAC (std_ss++QI_ss) [bir_exec_steps_observe_llist_def,
  LMAP_EQ_LNIL, llistTheory.LFILTER_EQ_NIL, bir_exec_step_NO_OBSERVE,
  llistTheory.every_def, llistTheory.exists_LNTH, combinTheory.o_DEF,
  llistTheory.LNTH_LGENLIST] >>
REPEAT STRIP_TAC >>
Cases_on `step_no` >> (
  FULL_SIMP_TAC std_ss []
));


val bir_exec_steps_observe_list_NO_OBSERVE = store_thm ("bir_exec_steps_observe_list_NO_OBSERVE",
``!p st step_no. (~(bir_program_contains_observe p)) ==>
     (bir_exec_steps_observe_list p st step_no = [])``,

SIMP_TAC std_ss [bir_exec_steps_observe_list_to_llist_THE,
  bir_exec_steps_observe_llist_NO_OBSERVE, llistTheory.toList_THM]);


val bir_exec_steps_GEN_NO_OBSERVE = store_thm ("bir_exec_steps_GEN_NO_OBSERVE",
``!pc_cond p st step_no.
     (~(bir_program_contains_observe p)) ==>
     case (bir_exec_steps_GEN pc_cond p st step_no) of
       | BER_Looping ll => (ll = [||])
       | BER_Ended ol c_st c_pc st' => (ol = [])``,

SIMP_TAC std_ss [bir_exec_steps_GEN_def, LET_THM, bir_exec_steps_observe_llist_NO_OBSERVE,
  llistTheory.toList_THM] >>
REPEAT STRIP_TAC >>
Cases_on `bir_exec_infinite_steps_COUNT_STEPS pc_cond step_no p st` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
));


val bir_exec_steps_NO_OBSERVE = store_thm ("bir_exec_steps_NO_OBSERVE",
``!p st. (~(bir_program_contains_observe p)) ==>
         case (bir_exec_steps p st) of
           | BER_Looping ll => (ll = [||])
           | BER_Ended ol c_st c_pc st' => (ol = [])``,
SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_GEN_NO_OBSERVE]);


val bir_exec_to_labels_n_NO_OBSERVE = store_thm ("bir_exec_to_labels_n_NO_OBSERVE",
``!ls step_no p st. (~(bir_program_contains_observe p)) ==>
         case (bir_exec_to_labels_n ls p st step_no) of
           | BER_Looping ll => (ll = [||])
           | BER_Ended ol c_st c_pc st' => (ol = [])``,
SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_steps_GEN_NO_OBSERVE]);


val bir_exec_step_n_NO_OBSERVE = store_thm ("bir_exec_step_n_NO_OBSERVE",
``!p st step_no. (~(bir_program_contains_observe p)) ==>
                 (FST (bir_exec_step_n p st step_no) = [])``,

REPEAT STRIP_TAC >>
`?ol c st'. (bir_exec_step_n p st step_no) = (ol, c, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [] >>
MP_TAC (Q.SPECL [`(T, \_. T)`, `p`, `st`, `SOME step_no`] bir_exec_steps_GEN_NO_OBSERVE) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_n_TO_steps_GEN]);


val bir_exec_block_n_NO_OBSERVE = store_thm ("bir_exec_block_n_NO_OBSERVE",
``!p st step_no. (~(bir_program_contains_observe p)) ==>
                 (FST (bir_exec_block_n p st step_no) = [])``,

REPEAT STRIP_TAC >>
`?ol c c' st'. (bir_exec_block_n p st step_no) = (ol, c, c', st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [] >>
MP_TAC (Q.SPECL [`(F, \pc. pc.bpc_index = 0)`, `p`, `st`, `SOME step_no`]
  bir_exec_steps_GEN_NO_OBSERVE) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_block_n_TO_steps_GEN]);




(***************************************************************)
(* for blocks                                                  *)
(***************************************************************)

val bir_exec_stmtsB_state_def = Define `
  bir_exec_stmtsB_state stmts (c, st) =
  SND (bir_exec_stmtsB stmts ([], c, st))`;


val bir_exec_stmtsB_state_THM = store_thm ("bir_exec_stmtsB_state_THM",
  ``!stmts l c st. SND (bir_exec_stmtsB stmts (l, c, st)) =
                   bir_exec_stmtsB_state stmts (c, st)``,

REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`l`] bir_exec_stmtsB_RESET_ACCUMULATOR) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_THM, bir_exec_stmtsB_state_def]);


val bir_exec_stmtsB_state_REWRS = store_thm ("bir_exec_stmtsB_state_REWRS",
  ``(!c st. bir_exec_stmtsB_state [] (c, st) = (c, st)) /\
    (!stmts c st. bir_state_is_terminated st ==>
       (bir_exec_stmtsB_state stmts (c, st) = (c, st))) /\
    (!stmts (stmt:'a bir_stmt_basic_t) c st. ~(bir_state_is_terminated st) ==>
       (bir_exec_stmtsB_state (stmt::stmts) (c, st) =
        bir_exec_stmtsB_state stmts (SUC c, bir_exec_stmtB_state stmt st)))``,

SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_exec_stmtsB_state_def, bir_exec_stmtsB_REWRS,
  LET_THM] >>
SIMP_TAC std_ss [bir_exec_stmtsB_state_THM, bir_exec_stmtB_state_def]);


val bir_exec_stmtsB_state_REWRS_COND = store_thm ("bir_exec_stmtsB_state_REWRS_COND",
  ``(!c st. (bir_exec_stmtsB_state [] (c, st) = (c, st))) /\
    (!stmt stmts c st. (bir_exec_stmtsB_state (stmt::stmts) (c, st) =
       if (bir_state_is_terminated st) then (c, st) else
       bir_exec_stmtsB_state stmts (SUC c, bir_exec_stmtB_state stmt st)))``,

METIS_TAC[bir_exec_stmtsB_state_REWRS]);

val bir_exec_block_state_def = Define `bir_exec_block_state p bl st =
  SND (bir_exec_block p bl st)`;


val bir_exec_stmtsB_NO_OBSERVE_THM = store_thm ("bir_exec_stmtsB_NO_OBSERVE_THM",
  ``!stmts l c st. ~(EXISTS bir_stmtB_is_observe stmts) ==>
         (FST (bir_exec_stmtsB stmts (l, c, st)) = REVERSE l)``,

Induct >- (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS]
) >>
FULL_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmtsB_REWRS_COND, combinTheory.o_DEF] >>
REPEAT STRIP_TAC >>
DISJ2_TAC >>
rename1 `~(bir_stmtB_is_observe stmt)` >>
`~(IS_SOME (FST (bir_exec_stmtB stmt st)))` by METIS_TAC[bir_exec_stmtB_only_observe_produces_observation] >>
`?fe st'. bir_exec_stmtB stmt st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [LET_THM, OPT_CONS_REWRS]);


val bir_exec_block_state_ALT_DEF = store_thm ("bir_exec_block_state_ALT_DEF",
 ``!p bl st. bir_exec_block_state p bl st =
  let (c, st') = bir_exec_stmtsB_state bl.bb_statements (0, st) in
  (if (bir_state_is_terminated st') then
    (c, st' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + PRE c))
  else
    (SUC c,
        let st'' = bir_exec_stmtE p bl.bb_last_statement st' in
        if (bir_state_is_terminated st'') then
          (st'' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + c))
        else st''))``,

SIMP_TAC (std_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) [
   bir_exec_block_state_def, bir_exec_block_def, LET_THM,
   bir_exec_stmtsB_state_THM]);


val bir_exec_block_NO_OBSERVE_THM = store_thm ("bir_exec_block_NO_OBSERVE_THM",
  ``!p bl st. ~(bir_block_contains_observe bl) ==>
         (FST (bir_exec_block p bl st) = [])``,

SIMP_TAC std_ss [bir_exec_block_def,
  bir_block_contains_observe_def] >>
SIMP_TAC (list_ss ++ pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) [
  LET_THM, bir_exec_stmtsB_NO_OBSERVE_THM]);


val bir_exec_block_DEF_NO_OBSERVE = store_thm ("bir_exec_block_DEF_NO_OBSERVE",
  ``!p bl st. ~(bir_block_contains_observe bl) ==>
         (bir_exec_block p bl st = ([], bir_exec_block_state p bl st))``,

REPEAT STRIP_TAC >>
`[] = FST (bir_exec_block p bl st)` by
  METIS_TAC[bir_exec_block_NO_OBSERVE_THM] >>
ASM_SIMP_TAC std_ss [bir_exec_block_state_def]);


val _ = export_theory();
