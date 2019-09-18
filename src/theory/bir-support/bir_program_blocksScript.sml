open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory;
open bir_expTheory bir_programTheory HolBACoreSimps
open bir_program_valid_stateTheory bir_program_terminationTheory;
open bir_program_multistep_propsTheory;
open bir_program_varsTheory
open bir_program_env_orderTheory
open bir_typing_progTheory bir_envTheory
open pred_setTheory

val _ = new_theory "bir_program_blocks";


(* ------------------------------------------------------------------------- *)
(* This theory tries to execute whole blocks in an easy way.
   The PC is only relevant for fetching the next instruction.
   Moreover, basic statements can only terminate or increment the PC. Therefore
   executing blocks can be simplified by executing one instruction after the
   other and only updating the PC at the very end.                             *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(*  PC only matters for fetching the next instruction                        *)
(* ------------------------------------------------------------------------- *)

val bir_states_EQ_EXCEPT_PC_def = Define `
  bir_states_EQ_EXCEPT_PC st1 st2 <=>
  ((st1 with bst_pc := ARB) = (st2 with bst_pc := ARB))`;

val bir_states_EQ_EXCEPT_PC_REWRS = save_thm ("bir_states_EQ_EXCEPT_PC_REWRS",
  SIMP_RULE (std_ss++holBACore_ss) [bir_state_t_component_equality]
    bir_states_EQ_EXCEPT_PC_def);

val bir_states_EQ_EXCEPT_PC_IS_EQUIV = store_thm ("bir_states_EQ_EXCEPT_PC_IS_EQUIV",
  ``(!st. bir_states_EQ_EXCEPT_PC st st) /\
    (!st1 st2. bir_states_EQ_EXCEPT_PC st1 st2 <=> (bir_states_EQ_EXCEPT_PC st2 st1)) /\
    (!st1 st2 st3. bir_states_EQ_EXCEPT_PC st1 st2 ==>
                   bir_states_EQ_EXCEPT_PC st2 st3 ==>
                   bir_states_EQ_EXCEPT_PC st1 st3)``,
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_states_EQ_EXCEPT_PC_REWRS]);


val bir_states_EQ_EXCEPT_PC_terminated = store_thm ("bir_states_EQ_EXCEPT_PC_terminated",
  ``!st1 st2. bir_states_EQ_EXCEPT_PC st1 st2 ==>
     (bir_state_is_terminated st1 = bir_state_is_terminated st2)``,
SIMP_TAC std_ss [bir_state_is_terminated_def, bir_states_EQ_EXCEPT_PC_REWRS]);

val bir_observation_states_EQ_EXCEPT_PC_def = Define `
  bir_observation_states_EQ_EXCEPT_PC ost1 ost2 = (
    (FST ost1 = FST ost2) /\ (bir_states_EQ_EXCEPT_PC (SND ost1) (SND ost2)))`;


val bir_observation_states_EQ_EXCEPT_PC_IS_EQUIV = store_thm ("bir_observation_states_EQ_EXCEPT_PC_IS_EQUIV",
  ``(!ost. bir_observation_states_EQ_EXCEPT_PC ost ost) /\
    (!ost1 ost2. bir_observation_states_EQ_EXCEPT_PC ost1 ost2 <=>
                 bir_observation_states_EQ_EXCEPT_PC ost2 ost1) /\
    (!ost1 ost2 ost3. bir_observation_states_EQ_EXCEPT_PC ost1 ost2 ==>
                      bir_observation_states_EQ_EXCEPT_PC ost2 ost3 ==>
                      bir_observation_states_EQ_EXCEPT_PC ost1 ost3)``,
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_states_EQ_EXCEPT_PC_REWRS,
  bir_observation_states_EQ_EXCEPT_PC_def]);


val bir_exec_stmtB_pc_unimportant = store_thm ("bir_exec_stmtB_pc_unimportant",
``!st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_observation_states_EQ_EXCEPT_PC (bir_exec_stmtB stmt st1) (bir_exec_stmtB stmt st2)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_def,
    bir_observation_states_EQ_EXCEPT_PC_def, bir_states_EQ_EXCEPT_PC_REWRS] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
));


val bir_exec_stmtE_pc_unimportant = store_thm ("bir_exec_stmtE_pc_unimportant",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_states_EQ_EXCEPT_PC (bir_exec_stmtE p stmt st1) (bir_exec_stmtE p stmt st2)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, LET_DEF,
    bir_exec_stmt_jmp_def, bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def,
    bir_exec_stmt_jmp_to_label_def,
    bir_states_EQ_EXCEPT_PC_REWRS] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
));


val bir_exec_stmtE_pc_unimportant_strong = store_thm ("bir_exec_stmtE_pc_unimportant_strong",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 /\ ~(bir_state_is_terminated (bir_exec_stmtE p stmt st1)) ==>
     (bir_exec_stmtE p stmt st1 = bir_exec_stmtE p stmt st2)``,

REPEAT GEN_TAC >> STRIP_TAC >>
POP_ASSUM MP_TAC >>
FULL_SIMP_TAC std_ss [bir_states_EQ_EXCEPT_PC_REWRS, bir_state_t_component_equality] >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, LET_DEF,
    bir_exec_stmt_jmp_def, bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def,
    bir_exec_stmt_jmp_to_label_def] >>
  REPEAT CASE_TAC >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def, bir_state_is_terminated_def]
));


val bir_exec_stmt_pc_unimportant = store_thm ("bir_exec_stmt_pc_unimportant",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_observation_states_EQ_EXCEPT_PC (bir_exec_stmt p stmt st1) (bir_exec_stmt p stmt st2)``,

Tactical.REVERSE (Cases_on `stmt`) >- (
  SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_stmtE_pc_unimportant,
    bir_observation_states_EQ_EXCEPT_PC_def]
) >>
REPEAT STRIP_TAC >>
rename1 `BStmtB stmt` >>
ASM_SIMP_TAC std_ss [bir_exec_stmt_def, LET_DEF] >>
`bir_observation_states_EQ_EXCEPT_PC (bir_exec_stmtB stmt st1) (bir_exec_stmtB stmt st2)` by
  METIS_TAC[bir_exec_stmtB_pc_unimportant] >>
FULL_SIMP_TAC (std_ss++holBACore_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) [
  bir_observation_states_EQ_EXCEPT_PC_def,
  bir_states_EQ_EXCEPT_PC_REWRS]);



(* ------------------------------------------------------------------------- *)
(*  Definition of executing lists of basic staments                          *)
(* ------------------------------------------------------------------------- *)

(* First, let's define executing lists of basic statements. *)
val bir_exec_stmtsB_def = Define `
  (bir_exec_stmtsB [] (l, c, st) = (REVERSE l, c, st)) /\
  (bir_exec_stmtsB (stmt::stmts) (l, c, st) =
     if (bir_state_is_terminated st) then (REVERSE l, c, st) else
     let (fe, st') = bir_exec_stmtB stmt st in
     bir_exec_stmtsB stmts (OPT_CONS fe l, SUC c, st'))`;


val bir_exec_stmtsB_exists =
  store_thm("bir_exec_stmtsB_exists",
  ``!stmtsB l c st.
      ?l' c' st'.
        bir_exec_stmtsB stmtsB (l,c,st) = (l', c', st')``,

Induct_on `stmtsB` >- (
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def] >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC std_ss []
) >>
ASSUME_TAC (SPECL [``h:'a bir_stmt_basic_t``, ``st:bir_state_t``]
                  bir_exec_stmtB_exists) >>
FULL_SIMP_TAC std_ss [LET_DEF]
);


val bir_exec_stmtsB_REWRS = store_thm ("bir_exec_stmtsB_REWRS",
  ``(!l c st. bir_exec_stmtsB [] (l, c, st) = (REVERSE l, c, st)) /\
    (!stmts l c st. bir_state_is_terminated st ==>
       (bir_exec_stmtsB stmts (l, c, st) = (REVERSE l, c, st))) /\
    (!stmts stmt l c st. ~(bir_state_is_terminated st) ==>
       (bir_exec_stmtsB (stmt::stmts) (l, c, st) =
        let (fe, st') = bir_exec_stmtB stmt st in
        bir_exec_stmtsB stmts (OPT_CONS fe l, SUC c, st')))``,

REPEAT STRIP_TAC >| [
  REWRITE_TAC [bir_exec_stmtsB_def],

  Cases_on `stmts` >> ASM_SIMP_TAC std_ss [bir_exec_stmtsB_def],

  ASM_SIMP_TAC std_ss [bir_exec_stmtsB_def]
]);


val bir_exec_stmtsB_REWRS_COND = store_thm ("bir_exec_stmtsB_REWRS_COND",
  ``(!l c st. (bir_exec_stmtsB [] (l, c, st) = (REVERSE l, c, st))) /\
    (!stmt stmts l c st. (bir_exec_stmtsB (stmt::stmts) (l, c, st) =
       if (bir_state_is_terminated st) then (REVERSE l, c, st) else
       let (fe, st') = bir_exec_stmtB stmt st in
       bir_exec_stmtsB stmts (OPT_CONS fe l, SUC c, st')))``,

METIS_TAC[bir_exec_stmtsB_REWRS]);


val bir_exec_stmtsB_APPEND = store_thm ("bir_exec_stmtsB_APPEND",
  ``!stmts1 stmts2 l c st. (bir_exec_stmtsB (stmts1 ++ stmts2) (l, c, st) =
       let (l', c', st') = bir_exec_stmtsB stmts1 (l, c, st) in
       bir_exec_stmtsB stmts2 (REVERSE l', c', st'))``,

Induct >- (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS, LET_THM]
) >>
REPEAT GEN_TAC >>
rename1 `stmt :: stmts1` >>
Cases_on `bir_state_is_terminated st` >| [
  ASM_SIMP_TAC list_ss [bir_exec_stmtsB_REWRS, LET_THM],

  ASM_SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [bir_exec_stmtsB_REWRS, LET_THM]
]);


val bir_exec_stmtsB_RESET_ACCUMULATOR_COUNTER = store_thm ("bir_exec_stmtsB_RESET_ACCUMULATOR_COUNTER",
  ``!l c stmts st. (bir_exec_stmtsB stmts (l, c, st) =
                   (let (l', c', st') = bir_exec_stmtsB stmts ([], 0, st) in
                   ((REVERSE l) ++ l', c+c', st')))``,
Induct_on `stmts` >- (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS_COND, LET_DEF]
) >>
REPEAT STRIP_TAC >>
rename1 `bir_exec_stmtsB (stmt::stmts)` >>
SIMP_TAC list_ss [bir_exec_stmtsB_REWRS_COND] >>
ONCE_ASM_REWRITE_TAC[] >>
POP_ASSUM (K ALL_TAC) >>
COND_CASES_TAC >- (
  ASM_SIMP_TAC list_ss [LET_DEF]
) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_DEF] >>
Cases_on `FST (bir_exec_stmtB stmt st)` >> (
  ASM_SIMP_TAC list_ss [OPT_CONS_REWRS]
));


val bir_exec_stmtsB_RESET_ACCUMULATOR = store_thm ("bir_exec_stmtsB_RESET_ACCUMULATOR",
  ``!l c stmts st. (bir_exec_stmtsB stmts (l, c, st) =
                   (let (l', c', st') = bir_exec_stmtsB stmts ([], c, st) in
                   ((REVERSE l) ++ l', c', st')))``,
ONCE_REWRITE_TAC [bir_exec_stmtsB_RESET_ACCUMULATOR_COUNTER] >>
SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [LET_DEF]);


val bir_exec_stmtsB_RESET_COUNTER = store_thm ("bir_exec_stmtsB_RESET_COUNTER",
  ``!l c stmts st. (bir_exec_stmtsB stmts (l, c, st) =
                   (let (l', c', st') = bir_exec_stmtsB stmts (l, 0, st) in
                   (l', c+c', st')))``,
ONCE_REWRITE_TAC [bir_exec_stmtsB_RESET_ACCUMULATOR_COUNTER] >>
SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [LET_DEF]);


val bir_exec_stmtsB_REWR_NO_STEP = store_thm ("bir_exec_stmtsB_REWR_NO_STEP",
  ``!l c st l' st' stmts. (bir_exec_stmtsB stmts (l, c, st) = (l', c, st')) <=>
       ((l' = REVERSE l) /\ (st' = st) /\
       ((bir_state_is_terminated st) \/ (stmts = [])))``,

Cases_on `stmts` >> (
  SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) [
    bir_exec_stmtsB_def, LET_DEF]
) >>
REPEAT GEN_TAC >>
DISJ2_TAC >>
ONCE_REWRITE_TAC[bir_exec_stmtsB_RESET_COUNTER] >>
SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) [LET_DEF]);


(* ------------------------------------------------------------------------- *)
(*  PC is also unimportant for these                                         *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmtsB_pc_unchanged = store_thm ("bir_exec_stmtsB_pc_unchanged",
``!stmts st1 st2 m c l l'.
     (bir_exec_stmtsB stmts (l, m, st1) = (l', c, st2)) ==>
     (st2.bst_pc = st1.bst_pc)``,

Induct >> (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >> COND_CASES_TAC >- (
  ASM_SIMP_TAC std_ss []
) >>
SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_THM,
  GSYM bir_exec_stmtB_state_def] >>
METIS_TAC[bir_exec_stmtB_pc_unchanged]);


val bir_exec_stmtsB_pc_unimportant = store_thm ("bir_exec_stmtsB_pc_unimportant",
``!stmts l st1 st2 st1' st2' m c1 c2 l1 l2.
     bir_states_EQ_EXCEPT_PC st1 st2 /\
     (bir_exec_stmtsB stmts (l, m, st1) = (l1, c1, st1')) /\
     (bir_exec_stmtsB stmts (l, m, st2) = (l2, c2, st2')) ==>

     ((l1 = l2) /\ (c1 = c2) /\ (bir_states_EQ_EXCEPT_PC st1' st2'))``,

Induct >> (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >> STRIP_TAC >>
rename1 `bir_exec_stmtB stmt` >>
`bir_state_is_terminated st2 = bir_state_is_terminated st1` by
  METIS_TAC[bir_states_EQ_EXCEPT_PC_terminated] >>
Cases_on `bir_state_is_terminated st1` >> (
  FULL_SIMP_TAC std_ss []
) >>
Q.PAT_X_ASSUM `!l st1 st2. _` MATCH_MP_TAC >>
`bir_observation_states_EQ_EXCEPT_PC (bir_exec_stmtB stmt st1)
       (bir_exec_stmtB stmt st2)` by METIS_TAC[bir_exec_stmtB_pc_unimportant] >>
`?fe1 st'1. bir_exec_stmtB stmt st1 = (fe1, st'1)` by METIS_TAC[pairTheory.PAIR] >>
`?fe2 st'2. bir_exec_stmtB stmt st2 = (fe2, st'2)` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [bir_observation_states_EQ_EXCEPT_PC_def,
  bir_states_EQ_EXCEPT_PC_REWRS, LET_THM, pairTheory.pair_case_thm] >>
METIS_TAC[]);



val bir_exec_stmtsB_pc_unimportant_EVAL = store_thm ("bir_exec_stmtsB_pc_unimportant_EVAL",
``!stmts st1 st2 st1' m c l l'.
     bir_states_EQ_EXCEPT_PC st1 st2 /\
     (bir_exec_stmtsB stmts (l, m, st1) = (l', c, st1')) ==>

     (bir_exec_stmtsB stmts (l, m, st2) = (l', c, (st1' with bst_pc := st2.bst_pc)))``,

REPEAT STRIP_TAC >>
`?l2 c2 st2'. bir_exec_stmtsB stmts (l, m, st2) = (l2, c2, st2')` by METIS_TAC[pairTheory.PAIR] >>

`(l2 = l') /\ (c2 = c) /\ bir_states_EQ_EXCEPT_PC st1' st2'` by METIS_TAC[bir_exec_stmtsB_pc_unimportant] >>
`(st2'.bst_pc = st2.bst_pc)` by METIS_TAC[bir_exec_stmtsB_pc_unchanged] >>
ASM_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_states_EQ_EXCEPT_PC_REWRS, bir_state_t_component_equality]);



(* ------------------------------------------------------------------------- *)
(*  Semantics of bir_exec_stmtsB                                             *)
(* ------------------------------------------------------------------------- *)

(* We can prove that executing a list of basic statements and then
   updating the PC is the same as executing multiple steps and then updating the pc. *)

val bir_exec_stmtsB_COUNTER = store_thm ("bir_exec_stmtsB_COUNTER",
  ``!stmts st l l' c c' st'. (bir_exec_stmtsB stmts (l, c, st) = (l', c', st')) ==>
                             (c <= c')``,
Induct >> (
  SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_exec_stmtsB_REWRS_COND, LET_THM]
) >>
REPEAT GEN_TAC >>
COND_CASES_TAC >- (
  ASM_SIMP_TAC arith_ss [bir_exec_stmtsB_REWRS]
) >>
STRIP_TAC >>
`SUC c <= c'` by METIS_TAC[] >>
DECIDE_TAC);


val bir_exec_stmtsB_COUNTER_EQ = store_thm ("bir_exec_stmtsB_COUNTER_EQ",
  ``!stmts st l l' c st'. (bir_exec_stmtsB stmts (l, c, st) = (l', c, st')) ==>
                             ((st' = st) /\ (l' = REVERSE l))``,

Cases_on `stmts` >> (
  SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_exec_stmtsB_REWRS_COND, LET_THM]
) >>
REPEAT GEN_TAC >>
COND_CASES_TAC >- (
  ASM_SIMP_TAC arith_ss [bir_exec_stmtsB_REWRS]
) >>
STRIP_TAC >>
`SUC c <= c` by METIS_TAC[bir_exec_stmtsB_COUNTER] >>
FULL_SIMP_TAC arith_ss []);


val bir_exec_stmtsB_not_terminated_COUNTER = store_thm ("bir_exec_stmtsB_not_terminated_COUNTER",
``!stmts m st c st' l l'.
  (bir_exec_stmtsB stmts (l, m, st) = (l', c, st')) /\
  (~(bir_state_is_terminated st')) ==>
  (c = (m + LENGTH stmts))``,

Induct >> (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >> COND_CASES_TAC >- (
  ASM_SIMP_TAC std_ss [] >> METIS_TAC[]
) >>
rename1 `bir_exec_stmtB stmt` >>
`?fe st'. bir_exec_stmtB stmt st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM, pairTheory.pair_case_thm] >>
STRIP_TAC >>
`c = SUC m + LENGTH (stmts)` by METIS_TAC[] >>
ASM_SIMP_TAC list_ss []);


val bir_exec_stmtsB_SEMANTICS = store_thm ("bir_exec_stmtsB_SEMANTICS",
``!p i bl c st m l0.
    (bir_get_program_block_info_by_label p (st.bst_pc.bpc_label) = SOME (i, bl)) /\
    (c + st.bst_pc.bpc_index <= LENGTH bl.bb_statements) ==> !n1 st1 n2 st2 l1 l2.

    (bir_exec_stmtsB (SEG c st.bst_pc.bpc_index bl.bb_statements) (l0, m, st) = (l1, n1, st1)) /\
    (bir_exec_step_n p st c = (l2, n2, st2)) ==>

    ((n2 = n1 - m) /\
     (l1 = REVERSE l0 ++ l2) /\
    (bir_states_EQ_EXCEPT_PC st1 st2) /\
    (st1.bst_pc = st.bst_pc) /\
    (st2.bst_pc = st.bst_pc with bpc_index := (st.bst_pc.bpc_index +
       (if bir_state_is_terminated st2 then PRE n2 else n2))))
``,

NTAC 3 GEN_TAC >> Induct_on `c` >- (
  SIMP_TAC (list_ss++holBACore_ss) [bir_exec_stmtsB_def, bir_exec_step_n_REWRS,
    bir_states_EQ_EXCEPT_PC_IS_EQUIV, bir_programcounter_t_component_equality,
    rich_listTheory.SEG]
) >>
REPEAT GEN_TAC >> STRIP_TAC >>
Q.ABBREV_TAC `stmts = SEG c (SUC st.bst_pc.bpc_index) bl.bb_statements` >>
Q.ABBREV_TAC `stmt = EL st.bst_pc.bpc_index bl.bb_statements` >>
ASM_SIMP_TAC arith_ss [SEG_SUC_LENGTH] >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC (list_ss++holBACore_ss) [bir_exec_stmtsB_REWRS, bir_exec_step_n_REWRS,
    bir_states_EQ_EXCEPT_PC_IS_EQUIV,
    bir_programcounter_t_component_equality]
) >>
`?fe st'. bir_exec_stmtB stmt st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
`st'.bst_pc = st.bst_pc` by METIS_TAC [bir_exec_stmtB_pc_unchanged,
   bir_exec_stmtB_state_def, pairTheory.SND] >>
ASM_SIMP_TAC arith_ss [
    bir_exec_step_n_REWRS, bir_exec_stmtsB_REWRS,
    bir_exec_step_def, bir_get_current_statement_def,
    bir_exec_stmt_def, LET_DEF] >>
Cases_on `bir_state_is_terminated st'` >- (
  ASM_SIMP_TAC (arith_ss++holBACore_ss) [bir_exec_stmtsB_REWRS, bir_exec_step_n_REWRS,
    bir_states_EQ_EXCEPT_PC_IS_EQUIV, bir_programcounter_t_component_equality,
    OPT_CONS_REVERSE]
) >>
ASM_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `st'' = st' with bst_pc updated_by bir_pc_next` >>
`(st''.bst_pc.bpc_label = st.bst_pc.bpc_label) /\
 (st''.bst_pc.bpc_index = SUC (st.bst_pc.bpc_index))` by (
  Q.UNABBREV_TAC `st''` >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_pc_next_def]
) >>
Q.PAT_X_ASSUM `!st. _` (MP_TAC o Q.SPECL [`st''`, `SUC m`, `OPT_CONS fe l0`]) >>
`?l1 n1 st1. bir_exec_stmtsB stmts (OPT_CONS fe l0, SUC m,st'') = (l1, n1, st1)` by
  METIS_TAC[pairTheory.PAIR] >>
`?l2 n2 st2. (bir_exec_step_n p st'' c = (l2,n2,st2))` by
  METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC arith_ss [] >>
STRIP_TAC >>
`SUC m <= n1` by METIS_TAC[bir_exec_stmtsB_COUNTER] >>

`bir_exec_stmtsB stmts (OPT_CONS fe l0, SUC m,st') = (l1, n1, st1 with bst_pc := st'.bst_pc)` by (
  MATCH_MP_TAC bir_exec_stmtsB_pc_unimportant_EVAL >>
  Q.EXISTS_TAC `st''` >>
  Q.UNABBREV_TAC `st''` >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_states_EQ_EXCEPT_PC_REWRS]
) >>

Q.UNABBREV_TAC `st''` >>
FULL_SIMP_TAC (arith_ss++holBACore_ss) [bir_pc_next_def,
  bir_states_EQ_EXCEPT_PC_REWRS, bir_programcounter_t_component_equality,
  OPT_CONS_REVERSE, GSYM listTheory.APPEND_ASSOC, OPT_CONS_APPEND,
  listTheory.APPEND] >>
Cases_on `bir_state_is_terminated st2` >> (
  ASM_SIMP_TAC arith_ss []
) >>
Cases_on `SUC m < n1` >> (
  ASM_SIMP_TAC arith_ss []
) >>
`n1 = SUC m` by DECIDE_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_COUNT_0] >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]);


val bir_get_current_block_def = Define `
  bir_get_current_block p pc = if pc.bpc_index <> 0 then NONE else
     (option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE (\ibl. SOME (SND ibl)))`;

val bir_get_current_block_SOME = store_thm ("bir_get_current_block_SOME",
  ``!p pc bl. (bir_get_current_block p pc = SOME bl) <=>
              (?i. (bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl)) /\
                  (pc.bpc_index = 0))``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_get_current_block_def] >>
CASE_TAC >>
SIMP_TAC (std_ss++QI_ss++boolSimps.EQUIV_EXTRACT_ss) []);


val bir_get_current_block_block_pc_IS_SOME = store_thm ("bir_get_current_block_block_pc_IS_SOME",
  ``!p l. IS_SOME (bir_get_current_block p (bir_block_pc l)) <=>
          MEM l (bir_labels_of_program p)``,

SIMP_TAC (std_ss++holBACore_ss) [optionTheory.IS_SOME_EXISTS, bir_get_current_block_SOME,
  bir_block_pc_def, bir_get_program_block_info_by_label_MEM] >>
METIS_TAC[]);


val bir_exec_stmtsB_SEMANTICS_WHOLE_BLOCK = store_thm ("bir_exec_stmtsB_SEMANTICS_WHOLE_BLOCK",
``!p bl st n1 st1 l1 n2 st2 l2.
    (bir_get_current_block p st.bst_pc = SOME bl) /\

    (bir_exec_stmtsB bl.bb_statements ([], 0, st) = (l1, n1, st1)) /\
    (bir_exec_step_n p st (LENGTH bl.bb_statements) = (l2, n2, st2)) ==>

    ((n2 = n1) /\ (l2 = l1) /\
    (bir_states_EQ_EXCEPT_PC st1 st2) /\
    (st1.bst_pc = st.bst_pc) /\
    (st2.bst_pc = st.bst_pc with bpc_index := (st.bst_pc.bpc_index +
       (if bir_state_is_terminated st2 then PRE n2 else n2))))
``,

REPEAT GEN_TAC >> STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_get_current_block_SOME] >>
rename1 `_ = SOME (i, bl)` >>
MP_TAC (Q.SPECL [`p`, `i`, `bl`, `LENGTH bl.bb_statements`, `st`, `0`, `[]`] bir_exec_stmtsB_SEMANTICS) >>
ASM_SIMP_TAC list_ss [rich_listTheory.SEG_LENGTH_ID]);


val bir_exec_stmtsB_not_jumped = store_thm ("bir_exec_stmtsB_not_jumped",
``!stmts l c st ll l' c' st'.
st.bst_status <> BST_JumpOutside ll ==>
(bir_exec_stmtsB stmts (l,c,st) = (l',c',st')) ==>
st'.bst_status <> BST_JumpOutside ll``,

Induct >- (
  SIMP_TAC std_ss [bir_exec_stmtsB_def]
) >>
REPEAT STRIP_TAC >>
rename1 `stmt::stmts` >>
FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def] >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC std_ss []
) >>
`?fe st'. bir_exec_stmtB stmt st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
Q.PAT_X_ASSUM `!l c st. _` (MP_TAC o Q.SPECL [`OPT_CONS fe l`, `SUC c`, `st''`, `ll`]) >>
ASM_SIMP_TAC std_ss [] >>
MP_TAC (Q.SPECL [`st`, `stmt`, `ll`] bir_exec_stmtB_status_not_jumped) >>
ASM_SIMP_TAC std_ss [bir_exec_stmtB_state_def]);


(* ------------------------------------------------------------------------- *)
(*  Semantics of whole blocks                                                *)
(* ------------------------------------------------------------------------- *)

(* Adding the final statement of a block, we can therefore easily derive
   nice semantics for whole blocks *)
val bir_block_size_def = Define `bir_block_size bl = SUC (LENGTH bl.bb_statements)`;


val bir_exec_block_def = Define `bir_exec_block (p:'a bir_program_t) (bl:'a bir_block_t) st =
  let (l, c, st') = bir_exec_stmtsB bl.bb_statements ([], 0, st) in
  (if (bir_state_is_terminated st') then
    (l, c, st' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + PRE c))
  else
    (l, SUC c,
        let st'' = bir_exec_stmtE p bl.bb_last_statement st' in
        if (bir_state_is_terminated st'') then
          (st'' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + c))
        else st''))`;


val bir_exec_block_exists =
  store_thm("bir_exec_block_exists",
  ``!prog bl st.
      ?l' c' st'.
        bir_exec_block prog bl st = (l', c', st')``,

Cases_on `prog` >>
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``bl.bb_statements:'a bir_stmt_basic_t list``,
                   ``[]: 'a list``, ``0:num``, ``st:bir_state_t``]
                  bir_exec_stmtsB_exists) >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `bir_state_is_terminated st'` >> (
  FULL_SIMP_TAC std_ss []
)
);


val bir_exec_block_REWR_TERMINATED = store_thm ("bir_exec_block_REWR_TERMINATED",
 ``!p bl st. bir_state_is_terminated st ==>
             (bir_exec_block p bl st = ([], 0, st))``,

SIMP_TAC (list_ss++holBACore_ss) [bir_exec_block_def, bir_exec_stmtsB_REWRS, LET_DEF,
  bir_state_t_component_equality, bir_programcounter_t_component_equality]);


val bir_exec_block_REWR_NO_STEP = store_thm ("bir_exec_block_REWR_NO_STEP",
 ``!p bl st. (bir_exec_block p bl st = (ol, 0, st')) <=>
             (ol = []) /\ (bir_state_is_terminated st) /\ (st' = st)``,

REPEAT GEN_TAC >>
SIMP_TAC (list_ss++holBACore_ss) [bir_exec_block_def] >>
`?l c st'. bir_exec_stmtsB bl.bb_statements ([],0,st) = (l,c,st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [LET_DEF] >>

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss++bir_TYPES_ss) [bir_state_t_component_equality,
  bir_programcounter_t_component_equality] >>
REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >- (
  FULL_SIMP_TAC list_ss [bir_exec_stmtsB_REWR_NO_STEP] >> (
    REPEAT BasicProvers.VAR_EQ_TAC >>
    FULL_SIMP_TAC arith_ss []
  )
) >- (
  FULL_SIMP_TAC list_ss [bir_exec_stmtsB_REWRS] >>
  REPEAT BasicProvers.VAR_EQ_TAC  >>
  ASM_SIMP_TAC std_ss []
));



val bir_exec_block_n_1_TO_step_n = store_thm ("bir_exec_block_n_1_TO_step_n",
``!p bl st.
    (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_block_n p st 1 = (
       let (ol, c, st') = bir_exec_step_n p st (bir_block_size bl) in
       (ol, c, (if (0 < c) /\ (bir_state_COUNT_PC (F, \pc. pc.bpc_index = 0) st') then 1 else 0), st')))``,

REPEAT STRIP_TAC >>
`?ol c st'. bir_exec_step_n p st (bir_block_size bl) = (ol, c, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_DEF] >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, bir_exec_block_n_TO_steps_GEN,
  bir_exec_steps_GEN_1_EQ_Ended] >>
Cases_on `c = 0` >- (
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
  FULL_SIMP_TAC std_ss [bir_block_size_def, bir_exec_infinite_steps_fun_REWRS]
) >>
ASM_SIMP_TAC arith_ss [] >>

FULL_SIMP_TAC std_ss [bir_get_current_block_SOME] >>

`!n. n < c ==> ((bir_exec_infinite_steps_fun p st n).bst_pc = (st.bst_pc with bpc_index := n))` by (
   Induct >- (
     ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_infinite_steps_fun_REWRS2,
       bir_programcounter_t_component_equality]
   ) >>
   STRIP_TAC >>
   `n < c` by DECIDE_TAC >>
   FULL_SIMP_TAC arith_ss [] >>
   `~bir_state_is_terminated (bir_exec_infinite_steps_fun p st (SUC n))` by METIS_TAC[] >>
   POP_ASSUM MP_TAC >>
   SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2,
      bir_exec_step_state_def, bir_exec_step_def] >>

   `?stmt. bir_get_current_statement p (st.bst_pc with bpc_index := n) = SOME (BStmtB stmt)` by (
      FULL_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_get_current_statement_SOME_B,
         bir_block_size_def]
   ) >>
   ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [GSYM bir_exec_stmt_state_def, LET_DEF,
     bir_exec_stmt_state_REWRS] >>
   ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_programcounter_t_component_equality,
     bir_pc_next_def, bir_exec_stmtB_pc_unchanged]
) >>
Q.ABBREV_TAC `cpc = \n. bir_state_COUNT_PC (F, \pc. pc.bpc_index = 0)
      (bir_exec_infinite_steps_fun p st n)` >>

ASM_SIMP_TAC std_ss [] >>
`!n. (0 < n /\ n < c) ==> ~(cpc n)` by (
   Q.UNABBREV_TAC `cpc` >>
   FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_COUNT_PC_def, bir_state_is_terminated_def]
) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `cpc c` >> ASM_SIMP_TAC std_ss [] >>
Cases_on `c < bir_block_size bl` >- ASM_SIMP_TAC std_ss [] >>
`c = bir_block_size bl` by DECIDE_TAC >>
Cases_on `c` >- FULL_SIMP_TAC std_ss [] >>

Q.PAT_X_ASSUM `~(cpc (SUC n))` MP_TAC >>
Q.UNABBREV_TAC `cpc` >>
ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2,
  bir_exec_step_state_def, bir_exec_step_def] >>

`?stmt. bir_get_current_statement p (st.bst_pc with bpc_index := n) = SOME (BStmtE stmt)` by (
   FULL_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_get_current_statement_SOME_E,
     bir_block_size_def]
) >>
ONCE_REWRITE_TAC [boolTheory.MONO_NOT_EQ] >>
SIMP_TAC std_ss [bir_state_COUNT_PC_def] >>

ASM_SIMP_TAC std_ss [bir_exec_stmt_def, bir_state_COUNT_PC_def,
  bir_exec_stmtE_block_pc] >>
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def]

);


val bir_exec_block_SEMANTICS_step_n = store_thm ("bir_exec_block_SEMANTICS_step_n",
``!p bl st.
    (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_block p bl st = bir_exec_step_n p st (bir_block_size bl))``,


REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC std_ss [bir_exec_block_REWR_TERMINATED, bir_exec_step_n_REWR_TERMINATED]
) >>
ASM_SIMP_TAC std_ss [bir_exec_block_def, bir_exec_step_n_SUC_END, bir_block_size_def] >>
REPEAT STRIP_TAC >>

`?l c st'. bir_exec_stmtsB bl.bb_statements ([], 0,st) = (l, c, st')` by METIS_TAC[pairTheory.PAIR] >>
`?l' c' st''. bir_exec_step_n p st (LENGTH bl.bb_statements) = (l', c', st'')` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `bl`, `st`] bir_exec_stmtsB_SEMANTICS_WHOLE_BLOCK) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >>
`bir_state_is_terminated st'' = bir_state_is_terminated st'` by
  METIS_TAC[bir_states_EQ_EXCEPT_PC_terminated] >>
Cases_on `bir_state_is_terminated st'` >- (
  FULL_SIMP_TAC std_ss [LET_DEF, bir_states_EQ_EXCEPT_PC_REWRS] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_t_component_equality]
) >>

`c = 0 + LENGTH bl.bb_statements` by METIS_TAC [bir_exec_stmtsB_not_terminated_COUNTER] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
`bir_exec_step p st'' = (NONE, bir_exec_stmtE p bl.bb_last_statement st'')` by (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_def, bir_get_current_statement_def,
    bir_exec_stmt_def, bir_get_current_block_SOME]
) >>
FULL_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [LET_DEF, OPT_CONS_REWRS] >>
COND_CASES_TAC >- (
  `bir_states_EQ_EXCEPT_PC (bir_exec_stmtE p bl.bb_last_statement st') (bir_exec_stmtE p bl.bb_last_statement st'')` by (
     MATCH_MP_TAC bir_exec_stmtE_pc_unimportant >>
     ASM_SIMP_TAC std_ss []
  ) >>
  `bir_state_is_terminated
         (bir_exec_stmtE p bl.bb_last_statement st'')` by
     METIS_TAC[bir_states_EQ_EXCEPT_PC_terminated] >>

  `(bir_exec_stmtE p bl.bb_last_statement st'' with bst_status := BST_Running) = st''` by
     METIS_TAC[bir_exec_stmtE_terminates_no_change] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_states_EQ_EXCEPT_PC_REWRS,
    bir_state_t_component_equality, bir_state_COUNT_PC_def]
) >- (
  MATCH_MP_TAC bir_exec_stmtE_pc_unimportant_strong >>
  ASM_SIMP_TAC std_ss []
));


val bir_exec_block_SEMANTICS = store_thm ("bir_exec_block_SEMANTICS",
``!p bl st.
    (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_block_n p st 1 = (
       let (ol, st_c, st') = bir_exec_block p bl st in
       (ol, st_c, (if (0 < st_c /\ bir_state_COUNT_PC (F, \pc. pc.bpc_index = 0) st') then 1 else 0), st')))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `bl`, `st`] bir_exec_block_n_1_TO_step_n) >>
ASM_SIMP_TAC std_ss [bir_exec_block_SEMANTICS_step_n]);



(* ------------------------------------------------------------------------- *)
(*  Executing whole programs blockwise                                       *)
(* ------------------------------------------------------------------------- *)

(* We can execute our whole program just using bir_exec_block,
   since we either terminate during execution of the next block
   or end up at the beginning of a new block.*)
val bir_exec_stmtE_new_block_pc = store_thm ("bir_exec_stmtE_new_block_pc",
  ``!st p stmt. let st' = bir_exec_stmtE p stmt st in
                ~(bir_state_is_terminated st') ==>
                IS_SOME (bir_get_current_block p st'.bst_pc)``,

REPEAT GEN_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def, LET_DEF, bir_exec_stmt_jmp_def,
    bir_state_is_terminated_def, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_halt_def, bir_exec_stmt_jmp_to_label_def] >>
  REPEAT CASE_TAC >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_get_current_block_block_pc_IS_SOME,
    bir_state_set_typeerror_def]
));


val bir_get_current_statement_NONE_stmt =
  store_thm("bir_get_current_statement_NONE_stmt",
  ``!prog pc.
      (bir_get_current_statement prog pc = NONE) ==>
      (bir_get_current_block prog pc = NONE)``,

FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_get_current_block_def,
               bir_get_current_statement_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_get_program_block_info_by_label
            prog pc.bpc_label` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >>
Cases_on `0 = LENGTH r.bb_statements` >>
Cases_on `0 < LENGTH r.bb_statements` >> (
  FULL_SIMP_TAC arith_ss []
)
);


val bir_exec_block_new_block_pc = store_thm ("bir_exec_block_new_block_pc",
``!p bl st st' c l.
    (bir_get_current_block p st.bst_pc = SOME bl) /\
    (bir_exec_block p bl st = (l, c, st')) /\
    ~(bir_state_is_terminated st') ==>
    (IS_SOME (bir_get_current_block p st'.bst_pc))``,

NTAC 3 GEN_TAC >>
`?l2 c2 st2. bir_exec_stmtsB bl.bb_statements ([], 0,st) = (l2, c2, st2)` by METIS_TAC[pairTheory.PAIR] >>
Cases_on `bir_state_is_terminated st2` >- (
  ASM_SIMP_TAC std_ss [bir_exec_block_def, LET_DEF] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
) >>
Cases_on `bir_state_is_terminated
        (bir_exec_stmtE p bl.bb_last_statement st2)` >- (
  ASM_SIMP_TAC std_ss [bir_exec_block_def, LET_DEF] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
) >>

ASM_SIMP_TAC std_ss [bir_exec_block_def, LET_DEF] >>
METIS_TAC [bir_exec_stmtE_new_block_pc, LET_DEF]);


val bir_exec_step_n_block = store_thm ("bir_exec_step_n_block",
  ``!p st bl n.
       (bir_get_current_block p st.bst_pc = SOME bl) /\
       (bir_block_size bl <= n) ==>

    (bir_exec_step_n p st n =
      let (l1, c1, st1) = bir_exec_block p bl st in
      let (l2, c2, st2) = bir_exec_step_n p st1 (n - bir_block_size bl) in
      (l1 ++ l2, c1+c2, st2))``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `n =  bir_block_size bl + (n - bir_block_size bl)` SUBST1_TAC >- DECIDE_TAC >>
REWRITE_TAC [bir_exec_step_n_add] >>
ASM_SIMP_TAC arith_ss [bir_exec_block_SEMANTICS_step_n]
);


val bir_exec_block_n_block = store_thm ("bir_exec_block_n_block",
  ``!p st bl n.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_block_n p st (SUC n) =
      let (l1, c1, st1) = bir_exec_block p bl st in
      let (l2, c2, c_bl2, st2) = bir_exec_block_n p st1 n in
      (l1 ++ l2, c1+c2, if (0 < c1 /\ bir_state_COUNT_PC (F, \pc. pc.bpc_index = 0) st1) then
          SUC c_bl2 else c_bl2, st2))``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `SUC n =  1 + n` SUBST1_TAC >- DECIDE_TAC >>
REWRITE_TAC [bir_exec_block_n_add] >>
MP_TAC (Q.SPECL [`p`, `bl`, `st`] bir_exec_block_SEMANTICS) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>

`?l1 c1 st1.  bir_exec_block p bl st = (l1, c1, st1)` by METIS_TAC[pairTheory.PAIR] >>
`?l2 c2 c_bl2 st2.  bir_exec_block_n p st1 n = (l2, c2, c_bl2, st2)` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [LET_DEF]);


val bir_exec_steps_block = store_thm ("bir_exec_steps_block",
  ``!p st bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_steps p st =
      let (l1, c1, st1) = bir_exec_block p bl st in
      case bir_exec_steps p st1 of
        BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
      | BER_Ended l2 c2 c2' st2 =>
        BER_Ended (l1++l2) (c1 + c2) (c1 + c2') st2)``,

REPEAT STRIP_TAC >>
`?l1 c1 st1. bir_exec_step_n p st (bir_block_size bl) = (l1, c1, st1)` by METIS_TAC[pairTheory.PAIR] >>

MP_TAC (Q.SPECL [`p`, `st`, `bir_block_size bl`] bir_exec_steps_combine) >>
FULL_SIMP_TAC std_ss [bir_exec_block_SEMANTICS_step_n, LET_DEF]);


val bir_exec_steps_block_GUARD = store_thm ("bir_exec_steps_block_GUARD",
  ``!p st bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_steps p st =
      let (l1, c1, st1) = bir_exec_block p bl st in
      if c1 < bir_block_size bl then BER_Ended l1 c1 c1 st1
      else (
        case bir_exec_steps p st1 of
          BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
        | BER_Ended l2 c2 c2' st2 =>
          BER_Ended (l1++l2) (c1 + c2) (c1 + c2') st2))``,

REPEAT STRIP_TAC >>
`?l1 c1 st1. bir_exec_step_n p st (bir_block_size bl) = (l1, c1, st1)` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `st`, `bir_block_size bl`] bir_exec_steps_combine_GUARD) >>
FULL_SIMP_TAC std_ss [bir_exec_block_SEMANTICS_step_n, LET_DEF]);


val bir_exec_to_labels_n_block = store_thm ("bir_exec_to_labels_n_block",
  ``!ls p st n bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_to_labels_n ls p st (SUC n) =
      let (l1, c1, st1) = bir_exec_block p bl st in
      let c1' = if (0 < c1) /\ (bir_state_COUNT_PC (F,
         \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) st1) then 1 else 0 in
      case bir_exec_to_labels_n ls p st1 (SUC n-c1') of
        BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
      | BER_Ended l2 c2 c2' st2 =>
        BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_to_labels_n_block_1] >>
MP_TAC (Q.SPECL [`p`, `bl`, `st`] bir_exec_block_SEMANTICS) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_DEF]);



val bir_exec_to_labels_block = store_thm ("bir_exec_to_labels_block",
  ``!ls p st bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_to_labels ls p st =
      let (l1, c1, st1) = bir_exec_block p bl st in
      if (0 < c1) /\ (bir_state_COUNT_PC (F,
         \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) st1) then
         BER_Ended l1 c1 1 st1
      else
      case bir_exec_to_labels ls p st1 of
        BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
      | BER_Ended l2 c2 c2' st2 =>
        BER_Ended (l1++l2) (c1 + c2) c2' st2)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_to_labels_def] >>
MP_TAC (Q.SPECL [`ls`, `p`, `st`, `0`, `bl`] bir_exec_to_labels_n_block) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss++bir_TYPES_ss) [LET_DEF,
  bir_exec_to_labels_n_REWR_0]);


(* ------------------------------------------------------------------------- *)
(*  Variables of blocks                                                      *)
(* ------------------------------------------------------------------------- *)

val bir_changed_vars_of_exec_stmtsB_THM = store_thm ("bir_changed_vars_of_exec_stmtsB_THM",
``!stmts st ol n.
   bir_env_EQ_FOR_VARS (bir_varset_COMPL (BIGUNION (IMAGE bir_changed_vars_of_stmtB (set stmts))))
        (let (ol', n', st') = (bir_exec_stmtsB stmts (ol, n, st)) in
         st'.bst_environ) (st.bst_environ)``,

Induct >- (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
REPEAT GEN_TAC >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC std_ss [bir_exec_stmtsB_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
rename1 `bir_exec_stmtsB (stmt::stmts)` >>
`?fe st'. bir_exec_stmtB stmt st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
`?ol' n' st''. bir_exec_stmtsB stmts (OPT_CONS fe ol, SUC n, st') =
               (ol', n', st'')` by METIS_TAC[pairTheory.PAIR] >>
Q.PAT_X_ASSUM `!st. _` (MP_TAC o Q.SPECL [`st'`, `OPT_CONS fe ol`, `SUC n`]) >>
MP_TAC (Q.SPECL [`st`, `stmt`] bir_changed_vars_of_stmtB_THM) >>
ASM_SIMP_TAC list_ss [LET_THM, IMAGE_INSERT, BIGUNION_INSERT, bir_varset_COMPL_UNION,
  bir_exec_stmtB_state_def, bir_exec_stmtsB_REWRS] >>
METIS_TAC[INTER_SUBSET, bir_env_EQ_FOR_VARS_SUBSET, bir_env_EQ_FOR_VARS_EQUIV]);


val bir_changed_vars_of_block_THM = store_thm ("bir_changed_vars_of_block_THM",
``!(p:'a bir_program_t) (bl:'a bir_block_t) st.
   (bir_env_EQ_FOR_VARS (bir_varset_COMPL (bir_changed_vars_of_block bl))
        (let (ol, n, st') = (bir_exec_block p bl st) in
         st'.bst_environ) (st.bst_environ))``,

REPEAT STRIP_TAC >>
`?ol n st'. bir_exec_stmtsB bl.bb_statements ([],0,st) = (ol, n, st')` by
  METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [` bl.bb_statements`, `st`, `[]`, `0`] bir_changed_vars_of_exec_stmtsB_THM) >>
ASM_SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [LET_THM, bir_exec_block_def,
  bir_changed_vars_of_block_def, bir_exec_stmtE_env_unchanged]);


val bir_vars_of_exec_stmtsB_THM = store_thm ("bir_vars_of_exec_stmtsB_THM",
``!vs (stmts :'a bir_stmt_basic_t list) st1 st2 l n.
    (BIGUNION (IMAGE bir_vars_of_stmtB (set stmts)) SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (ol1, n1, st1') = bir_exec_stmtsB stmts (l, n, st1) in
     let (ol2, n2, st2') = bir_exec_stmtsB stmts (l, n, st2) in
     ((ol1 = ol2) /\ (n1 = n2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))``,

GEN_TAC >>
Induct >- (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
REPEAT STRIP_TAC >>
`bir_state_is_terminated st1 = bir_state_is_terminated st2` by
   FULL_SIMP_TAC std_ss [bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def] >>
Cases_on `bir_state_is_terminated st2` >- (
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
rename1 `bir_exec_stmtsB (stmt::stmts)` >>
`?fe1 st1'. bir_exec_stmtB stmt st1 = (fe1, st1')` by METIS_TAC[pairTheory.PAIR] >>
`?fe2 st2'. bir_exec_stmtB stmt st2 = (fe2, st2')` by METIS_TAC[pairTheory.PAIR] >>
`?ol1 n1 st1''. bir_exec_stmtsB stmts (OPT_CONS fe1 l, SUC n, st1') =
               (ol1, n1, st1'')` by METIS_TAC[pairTheory.PAIR] >>
`?ol2 n2 st2''. bir_exec_stmtsB stmts (OPT_CONS fe2 l, SUC n, st2') =
               (ol2, n2, st2'')` by METIS_TAC[pairTheory.PAIR] >>
Q.PAT_X_ASSUM `!st. _` (MP_TAC o Q.SPECL [`st1'`, `st2'`, `OPT_CONS fe1 l`, `SUC n`]) >>
MP_TAC (Q.SPECL [`st1`, `st2`, `vs`, `stmt`] bir_vars_of_stmtB_THM) >>
FULL_SIMP_TAC list_ss [bir_exec_stmtsB_REWRS, LET_THM,
  IMAGE_INSERT, BIGUNION_INSERT, UNION_SUBSET] >>
NTAC 2 STRIP_TAC >>
REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC std_ss []);



val bir_vars_of_block_THM = store_thm ("bir_vars_of_block_THM",
``!(p : 'a bir_program_t) vs (bl :'a bir_block_t) st1 st2.
    (bir_vars_of_block bl SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (ol1, n1, st1') = bir_exec_block p bl st1 in
     let (ol2, n2, st2') = bir_exec_block p bl st2 in
     ((ol1 = ol2) /\ (n1 = n2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))``,

REPEAT STRIP_TAC >>
`?ol1 n1 st1'. bir_exec_stmtsB bl.bb_statements ([],0,st1) = (ol1, n1, st1')` by
  METIS_TAC[pairTheory.PAIR] >>
`?ol2 n2 st2'. bir_exec_stmtsB bl.bb_statements ([],0,st2) = (ol2, n2, st2')` by
  METIS_TAC[pairTheory.PAIR] >>
`(ol1 = ol2) /\ (n1 = n2) /\ bir_state_EQ_FOR_VARS vs st1' st2'` by (
  MP_TAC (Q.SPECL [`vs`, `bl.bb_statements`, `st1`, `st2`, `[]`, `0`] bir_vars_of_exec_stmtsB_THM) >>
  FULL_SIMP_TAC std_ss [bir_vars_of_block_def, UNION_SUBSET, LET_THM]
) >>
REPEAT BasicProvers.VAR_EQ_TAC >>

MP_TAC (Q.SPECL [`st1'`, `st2'`, `vs`, `p`, `bl.bb_last_statement`] bir_vars_of_stmtE_THM) >>
`bir_vars_of_stmtE bl.bb_last_statement SUBSET vs` by (
  FULL_SIMP_TAC std_ss [bir_vars_of_block_def, UNION_SUBSET]
) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_state_EQ_FOR_VARS_ALT_DEF] >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss++boolSimps.LIFT_COND_ss) [bir_exec_block_def, LET_THM,
  bir_state_COUNT_PC_def, bir_block_pc_def,
  bir_program_valid_stateTheory.bir_exec_stmtE_env_unchanged,
  bir_state_is_terminated_def]);



(* ------------------------------------------------------------------------- *)
(*  Env order                                                                *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmtsB_ENV_ORDER = store_thm ("bir_exec_stmtsB_ENV_ORDER",
``!stmts l n st.
  bir_env_order st.bst_environ
    (SND (SND (bir_exec_stmtsB stmts (l, n, st)))).bst_environ``,

Induct >> (
  SIMP_TAC std_ss [bir_exec_stmtsB_def, bir_env_oldTheory.bir_env_order_REFL]
) >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++pairSimps.gen_beta_ss) [bir_exec_stmtsB_def,
  bir_env_oldTheory.bir_env_order_REFL, LET_THM,
  GSYM bir_exec_stmtB_state_def] >>
METIS_TAC[bir_exec_stmtB_ENV_ORDER, bir_env_oldTheory.bir_env_order_TRANS]);


val bir_exec_block_ENV_ORDER = store_thm ("bir_exec_block_ENV_ORDER",
``!p st bl.
  bir_env_order st.bst_environ
    (SND (SND (bir_exec_block p bl st))).bst_environ``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++pairSimps.gen_beta_ss++bir_TYPES_ss) [
  bir_exec_block_def, LET_THM,
  bir_exec_stmtsB_ENV_ORDER, bir_exec_stmtE_env_unchanged]);


val _ = export_theory();
