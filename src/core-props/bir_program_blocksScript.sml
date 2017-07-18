open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory;
open bir_expTheory bir_programTheory HolBACoreSimps
open bir_program_valid_stateTheory bir_program_terminationTheory;


val _ = new_theory "bir_program_blocks";


(* ------------------------------------------------------------------------- *)
(* This theory tries to execute whole blocks in an easy way.
   The PC is only relevant for fetching the next instruction.
   Moreover, basic staments can only terminate or increment the PC. Therefore
   executing blocks can be simplified by executing one instruction after the
   other and just update the PC at the very end.                             *)
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


val bir_exec_stmtB_pc_unimportant = store_thm ("bir_exec_stmtB_pc_unimportant",
``!st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_states_EQ_EXCEPT_PC (bir_exec_stmtB stmt st1) (bir_exec_stmtB stmt st2)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_states_EQ_EXCEPT_PC_REWRS] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
));


val bir_exec_stmtE_pc_unimportant = store_thm ("bir_exec_stmtE_pc_unimportant",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_states_EQ_EXCEPT_PC (bir_exec_stmtE p stmt st1) (bir_exec_stmtE p stmt st2)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, LET_DEF,
    bir_exec_stmt_jmp_def, bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def,
    bir_states_EQ_EXCEPT_PC_REWRS] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
));


val bir_exec_stmtE_pc_unimportant_strong = store_thm ("bir_exec_stmtE_pc_unimportant_strong",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 /\ ~(bir_state_is_terminated (bir_exec_stmtE p stmt st1)) ==>
     (bir_exec_stmtE p stmt st1 = bir_exec_stmtE p stmt st2)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_states_EQ_EXCEPT_PC_REWRS, bir_state_t_component_equality] >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, LET_DEF,
    bir_exec_stmt_jmp_def, bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def] >>
  REPEAT CASE_TAC >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def, bir_state_is_terminated_def]
));


val bir_exec_stmt_pc_unimportant = store_thm ("bir_exec_stmt_pc_unimportant",
``!p st1 st2 stmt.
     bir_states_EQ_EXCEPT_PC st1 st2 ==>
     bir_states_EQ_EXCEPT_PC (bir_exec_stmt p stmt st1) (bir_exec_stmt p stmt st2)``,

Tactical.REVERSE (Cases_on `stmt`) >- (
  SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_stmtE_pc_unimportant]
) >>
REPEAT STRIP_TAC >>
rename1 `BStmtB stmt` >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmt_def, LET_DEF] >>
`bir_states_EQ_EXCEPT_PC (bir_exec_stmtB stmt st1) (bir_exec_stmtB stmt st2)` by
  METIS_TAC[bir_exec_stmtB_pc_unimportant] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_states_EQ_EXCEPT_PC_REWRS]);




(* ------------------------------------------------------------------------- *)
(*  Definition of executing lists of basic staments                          *)
(* ------------------------------------------------------------------------- *)

(* First lets define executing lists of basic statements. *)
val bir_exec_stmtsB_def = Define `
  (bir_exec_stmtsB [] (c, st) = (c, st)) /\
  (bir_exec_stmtsB (stmt::stmts) (c, st) =
     if (bir_state_is_terminated st) then (c, st) else
     bir_exec_stmtsB stmts (SUC c, bir_exec_stmtB stmt st))`;

val bir_exec_stmtsB_REWRS = store_thm ("bir_exec_stmtsB_REWRS",
  ``(!cst. bir_exec_stmtsB [] cst = cst) /\
    (!stmts c st. bir_state_is_terminated st ==> (bir_exec_stmtsB stmts (c, st) = (c, st))) /\
    (!stmts stmt c st. ~(bir_state_is_terminated st) ==>
       (bir_exec_stmtsB (stmt::stmts) (c, st) =
        bir_exec_stmtsB stmts (SUC c, bir_exec_stmtB stmt st)))``,

REPEAT STRIP_TAC >| [
  Cases_on `cst` >> REWRITE_TAC [bir_exec_stmtsB_def],

  Cases_on `stmts` >> ASM_SIMP_TAC std_ss [bir_exec_stmtsB_def],

  ASM_SIMP_TAC std_ss [bir_exec_stmtsB_def]
]);

val bir_exec_stmtsB_REWRS_COND = store_thm ("bir_exec_stmtsB_REWRS_COND",
  ``(!cst. bir_exec_stmtsB [] cst = cst) /\
    (!stmts stmt c st.
       (bir_exec_stmtsB (stmt::stmts) (c, st) =
        (if (bir_state_is_terminated st) then (c, st) else
         bir_exec_stmtsB stmts (SUC c, bir_exec_stmtB stmt st))))``,

METIS_TAC[bir_exec_stmtsB_REWRS]);



(* ------------------------------------------------------------------------- *)
(*  PC is also unimportant for these                                         *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmtsB_pc_unchanged = store_thm ("bir_exec_stmtsB_pc_unchanged",
``!stmts st1 st2 m c.
     (bir_exec_stmtsB stmts (m, st1) = (c, st2)) ==>
     (st2.bst_pc = st1.bst_pc)``,

Induct >> (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >> COND_CASES_TAC >- (
  ASM_SIMP_TAC std_ss []
) >>
METIS_TAC[bir_exec_stmtB_pc_unchanged]);


val bir_exec_stmtsB_pc_unimportant = store_thm ("bir_exec_stmtsB_pc_unimportant",
``!stmts st1 st2 st1' st2' m c1 c2.
     bir_states_EQ_EXCEPT_PC st1 st2 /\
     (bir_exec_stmtsB stmts (m, st1) = (c1, st1')) /\
     (bir_exec_stmtsB stmts (m, st2) = (c2, st2')) ==>

     ((c1 = c2) /\ (bir_states_EQ_EXCEPT_PC st1' st2'))``,

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
Q.PAT_X_ASSUM `!st1 st2. _` MATCH_MP_TAC >>
Q.EXISTS_TAC `bir_exec_stmtB stmt st1` >>
Q.EXISTS_TAC `bir_exec_stmtB stmt st2` >>
Q.EXISTS_TAC `SUC m` >>
ASM_SIMP_TAC std_ss [] >>
METIS_TAC[bir_exec_stmtB_pc_unimportant]);


val bir_exec_stmtsB_pc_unimportant_EVAL = store_thm ("bir_exec_stmtsB_pc_unimportant_EVAL",
``!stmts st1 st2 st1' m c.
     bir_states_EQ_EXCEPT_PC st1 st2 /\
     (bir_exec_stmtsB stmts (m, st1) = (c, st1')) ==>

     (bir_exec_stmtsB stmts (m, st2) = (c, (st1' with bst_pc := st2.bst_pc)))``,

REPEAT STRIP_TAC >>
`?c2 st2'. bir_exec_stmtsB stmts (m, st2) = (c2, st2')` by METIS_TAC[pairTheory.PAIR] >>

`(c2 = c) /\ bir_states_EQ_EXCEPT_PC st1' st2'` by METIS_TAC[bir_exec_stmtsB_pc_unimportant] >>
`(st2'.bst_pc = st2.bst_pc)` by METIS_TAC[bir_exec_stmtsB_pc_unchanged] >>
ASM_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_states_EQ_EXCEPT_PC_REWRS, bir_state_t_component_equality]);



(* ------------------------------------------------------------------------- *)
(*  Semantics of bir_exec_stmtsB                                             *)
(* ------------------------------------------------------------------------- *)

(* We can proof that the executing a list of basic statements and then
   updating the PC is the same as executing multiple steps and then updating the pc. *)

val bir_exec_stmtsB_COUNTER = store_thm ("bir_exec_stmtsB_COUNTER",
  ``!stmts st c c' st'. (bir_exec_stmtsB stmts (c, st) = (c', st')) ==>
                        (c <= c')``,
Induct >> (
  SIMP_TAC std_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >>
COND_CASES_TAC >- (
  ASM_SIMP_TAC arith_ss [bir_exec_stmtsB_REWRS]
) >>
STRIP_TAC >>
`SUC c <= c'` by METIS_TAC[] >>
DECIDE_TAC);


val bir_exec_stmtsB_not_terminated_COUNTER = store_thm ("bir_exec_stmtsB_not_terminated_COUNTER",
``!stmts m st c st'.
  (bir_exec_stmtsB stmts (m, st) = (c, st')) /\
  (~(bir_state_is_terminated st')) ==>
  (c = (m + LENGTH stmts))``,

Induct >> (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS_COND]
) >>
REPEAT GEN_TAC >> COND_CASES_TAC >- (
  ASM_SIMP_TAC std_ss [] >> METIS_TAC[]
) >>
STRIP_TAC >>
`c = SUC m + LENGTH (stmts)` by METIS_TAC[] >>
ASM_SIMP_TAC list_ss []);


val bir_exec_stmtsB_SEMANTICS = store_thm ("bir_exec_stmtsB_SEMANTICS",
``!p i bl c st m.
    (bir_get_program_block_info_by_label p (st.bst_pc.bpc_label) = SOME (i, bl)) /\
    (c + st.bst_pc.bpc_index <= LENGTH bl.bb_statements) ==> !n1 st1 n2 st2.

    (bir_exec_stmtsB (SEG c st.bst_pc.bpc_index bl.bb_statements) (m, st) = (n1, st1)) /\
    (bir_exec_step_n p st c = (n2, st2)) ==>

    ((n2 = n1 - m) /\
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
GEN_TAC >> GEN_TAC >> STRIP_TAC >>
Q.ABBREV_TAC `stmts = SEG c (SUC st.bst_pc.bpc_index) bl.bb_statements` >>
Q.ABBREV_TAC `stmt = EL st.bst_pc.bpc_index bl.bb_statements` >>
ASM_SIMP_TAC arith_ss [SEG_SUC_LENGTH] >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtsB_REWRS, bir_exec_step_n_REWRS,
    bir_states_EQ_EXCEPT_PC_IS_EQUIV,
    bir_programcounter_t_component_equality]
) >>
Q.ABBREV_TAC `st' = bir_exec_stmtB stmt st` >>
`st'.bst_pc = st.bst_pc` by METIS_TAC [bir_exec_stmtB_pc_unchanged] >>
ASM_SIMP_TAC arith_ss [
    bir_exec_step_n_REWRS, bir_exec_stmtsB_REWRS,
    bir_exec_step_def, bir_get_current_statement_def,
    bir_exec_stmt_def, LET_DEF] >>
Cases_on `bir_state_is_terminated st'` >- (
  ASM_SIMP_TAC (arith_ss++holBACore_ss) [bir_exec_stmtsB_REWRS, bir_exec_step_n_REWRS,
    bir_states_EQ_EXCEPT_PC_IS_EQUIV, bir_programcounter_t_component_equality]
) >>
ASM_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `st'' = st' with bst_pc updated_by bir_pc_next` >>
`(st''.bst_pc.bpc_label = st.bst_pc.bpc_label) /\
 (st''.bst_pc.bpc_index = SUC (st.bst_pc.bpc_index))` by (
  Q.UNABBREV_TAC `st''` >>
  ASM_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_pc_next_def]
) >>
Q.PAT_X_ASSUM `!st. _` (MP_TAC o Q.SPECL [`st''`, `SUC m`]) >>

`?n1 st1. bir_exec_stmtsB stmts (SUC m,st'') = (n1, st1)` by
  METIS_TAC[pairTheory.PAIR] >>
`?n2 st2. (bir_exec_step_n p st'' c = (n2,st2))` by
  METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC arith_ss [] >>
STRIP_TAC >>
`SUC m <= n1` by METIS_TAC[bir_exec_stmtsB_COUNTER] >>

`bir_exec_stmtsB stmts (SUC m,st') = (n1, st1 with bst_pc := st'.bst_pc)` by (
  MATCH_MP_TAC bir_exec_stmtsB_pc_unimportant_EVAL >>
  Q.EXISTS_TAC `st''` >>
  Q.UNABBREV_TAC `st''` >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_states_EQ_EXCEPT_PC_REWRS]
) >>

Q.UNABBREV_TAC `st''` >>
FULL_SIMP_TAC (arith_ss++holBACore_ss++holBACore_ss) [bir_pc_next_def,
  bir_states_EQ_EXCEPT_PC_REWRS, bir_programcounter_t_component_equality] >>
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



val bir_exec_stmtsB_SEMANTICS_WHOLE_BLOCK = store_thm ("bir_exec_stmtsB_SEMANTICS_WHOLE_BLOCK",
``!p bl st n1 st1 n2 st2.
    (bir_get_current_block p st.bst_pc = SOME bl) /\

    (bir_exec_stmtsB bl.bb_statements (0, st) = (n1, st1)) /\
    (bir_exec_step_n p st (LENGTH bl.bb_statements) = (n2, st2)) ==>

    ((n2 = n1) /\
    (bir_states_EQ_EXCEPT_PC st1 st2) /\
    (st1.bst_pc = st.bst_pc) /\
    (st2.bst_pc = st.bst_pc with bpc_index := (st.bst_pc.bpc_index +
       (if bir_state_is_terminated st2 then PRE n2 else n2))))
``,

REPEAT GEN_TAC >> STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_get_current_block_SOME] >>
rename1 `_ = SOME (i, bl)` >>
MP_TAC (Q.SPECL [`p`, `i`, `bl`, `LENGTH bl.bb_statements`, `st`, `0`] bir_exec_stmtsB_SEMANTICS) >>
ASM_SIMP_TAC list_ss [rich_listTheory.SEG_LENGTH_ID]);



(* ------------------------------------------------------------------------- *)
(*  Semantics of whole blocks                                                *)
(* ------------------------------------------------------------------------- *)

(* Adding the final statement of a block, we can therefore easily derive
   nice semantics for whole blocks *)

val bir_block_size_def = Define `bir_block_size bl = SUC (LENGTH bl.bb_statements)`;

val bir_exec_block_def = Define `bir_exec_block p bl st =
  let (c, st') = bir_exec_stmtsB bl.bb_statements (0, st) in
  (if (bir_state_is_terminated st') then
    (c, st' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + PRE c))
  else
    (SUC c,
        let st'' = bir_exec_stmtE p bl.bb_last_statement st' in
        if (bir_state_is_terminated st'') then
          (st'' with bst_pc := (st.bst_pc with bpc_index := st.bst_pc.bpc_index + c))
        else st''))`;


val bir_exec_block_terminated = store_thm ("bir_exec_block_terminated",
 ``!p bl st. bir_state_is_terminated st ==>
             (bir_exec_block p bl st = (0, st))``,

SIMP_TAC (std_ss++holBACore_ss ++ holBACore_ss) [bir_exec_block_def, bir_exec_stmtsB_REWRS, LET_DEF,
  bir_state_t_component_equality, bir_programcounter_t_component_equality]);


val bir_exec_block_SEMANTICS = store_thm ("bir_exec_block_SEMANTICS",
``!p bl st.
    (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_block p bl st = bir_exec_step_n p st (bir_block_size bl))``,


SIMP_TAC std_ss [bir_exec_block_def, arithmeticTheory.ADD1,
  bir_exec_step_n_add, bir_exec_step_n_REWRS, bir_block_size_def] >>
REPEAT STRIP_TAC >>

`?c st'. bir_exec_stmtsB bl.bb_statements (0,st) = (c, st')` by METIS_TAC[pairTheory.PAIR] >>
`?c' st''. bir_exec_step_n p st (LENGTH bl.bb_statements) = (c', st'')` by METIS_TAC[pairTheory.PAIR] >>
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
`bir_exec_step p st'' = bir_exec_stmtE p bl.bb_last_statement st''` by (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_def, bir_get_current_statement_def,
    bir_exec_stmt_def, bir_get_current_block_SOME]
) >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [LET_DEF] >>
COND_CASES_TAC >| [
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
    bir_state_t_component_equality],


  MATCH_MP_TAC bir_exec_stmtE_pc_unimportant_strong >>
  ASM_SIMP_TAC std_ss []
]);



(* ------------------------------------------------------------------------- *)
(*  Executing whole programs blockwise                                       *)
(* ------------------------------------------------------------------------- *)

(* We can execute our whole program just using bir_exec_block,
   size we either terminate during execution of the next block
   or end up at the beginning of a new block.*)

val bir_get_current_block_block_pc = store_thm ("bir_get_current_block_block_pc",
  ``!p l. IS_SOME (bir_get_current_block p (bir_block_pc l)) <=>
          MEM l (bir_labels_of_program p)``,

SIMP_TAC (std_ss++holBACore_ss) [optionTheory.IS_SOME_EXISTS, bir_get_current_block_SOME,
  bir_block_pc_def, bir_get_program_block_info_by_label_MEM] >>
METIS_TAC[]);


val bir_exec_stmtE_new_block_pc = store_thm ("bir_exec_stmtE_new_block_pc",
  ``!st p stmt. let st' = bir_exec_stmtE p stmt st in
                ~(bir_state_is_terminated st') ==>
                IS_SOME (bir_get_current_block p st'.bst_pc)``,

REPEAT GEN_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def, LET_DEF, bir_exec_stmt_jmp_def,
    bir_state_is_terminated_def, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_halt_def] >>
  REPEAT CASE_TAC >>
  ASM_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_get_current_block_block_pc,
    bir_state_set_failed_def]
));


val bir_exec_block_new_block_pc = store_thm ("bir_exec_block_new_block_pc",
``!p bl st st' c.
    (bir_get_current_block p st.bst_pc = SOME bl) /\
    (bir_exec_block p bl st = (c, st')) /\
    ~(bir_state_is_terminated st') ==>
    (IS_SOME (bir_get_current_block p st'.bst_pc))``,

NTAC 3 GEN_TAC >>
`?c2 st2. bir_exec_stmtsB bl.bb_statements (0,st) = (c2, st2)` by METIS_TAC[pairTheory.PAIR] >>
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
METIS_TAC [bir_exec_stmtE_new_block_pc]);


val bir_exec_step_n_block = store_thm ("bir_exec_step_n_block",
  ``!p st bl n.
       (bir_get_current_block p st.bst_pc = SOME bl) /\
       (bir_block_size bl <= n) ==>

    (bir_exec_step_n p st n =
      let (c1, st1) = bir_exec_block p bl st in
      let (c2, st2) = bir_exec_step_n p st1 (n - bir_block_size bl) in
      (c1+c2, st2))``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `n =  bir_block_size bl + (n - bir_block_size bl)` SUBST1_TAC >- DECIDE_TAC >>
REWRITE_TAC [bir_exec_step_n_add] >>
ASM_SIMP_TAC arith_ss [bir_exec_block_SEMANTICS]);



val bir_exec_steps_block = store_thm ("bir_exec_steps_block",
  ``!p st bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_steps p st =
      let (c1, st1) = bir_exec_block p bl st in
      case bir_exec_steps p st1 of
        NONE => NONE
      | SOME (c2,st2) => SOME (c1 + c2,st2))``,

REPEAT STRIP_TAC >>
`?c1 st1. bir_exec_step_n p st (bir_block_size bl) = (c1, st1)` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `st`, `bir_block_size bl`] bir_exec_steps_combine) >>
FULL_SIMP_TAC std_ss [bir_exec_block_SEMANTICS, LET_DEF])


val bir_exec_steps_block_GUARD = store_thm ("bir_exec_steps_block_GUARD",
  ``!p st bl.
       (bir_get_current_block p st.bst_pc = SOME bl) ==>

    (bir_exec_steps p st =
      let (c1, st1) = bir_exec_block p bl st in
      if c1 < bir_block_size bl then SOME (c1,st1)
      else
        case bir_exec_steps p st1 of
          NONE => NONE
        | SOME (c2,st2) => SOME (c1 + c2,st2))``,

REPEAT STRIP_TAC >>
`?c1 st1. bir_exec_step_n p st (bir_block_size bl) = (c1, st1)` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `st`, `bir_block_size bl`] bir_exec_steps_combine_GUARD) >>
FULL_SIMP_TAC std_ss [bir_exec_block_SEMANTICS, LET_DEF])



val _ = export_theory();
