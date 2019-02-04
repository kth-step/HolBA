open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_programTheory;
open bir_program_valid_stateTheory;
open llistTheory wordsLib pred_setTheory;
open HolBACoreSimps

open bir_auxiliaryTheory;

val _ = new_theory "bir_program_multistep_props";

(* ------------------------------------------------------------------------- *)
(* The definitions of executing multiple steps are not well suited for
   reasoning with directly. In this theory, some basic properties and rewrite
   rules are derived for them.                                               *)
(* ------------------------------------------------------------------------- *)


(***************************)
(* bir_exec_infinite_steps *)
(***************************)

val bir_exec_infinite_steps_fun_REWRS2 = store_thm ("bir_exec_infinite_steps_fun_REWRS2",
``(!p st. (bir_exec_infinite_steps_fun p st 0 = st)) /\
  (!p st n. (bir_exec_infinite_steps_fun p st (SUC n) =
     bir_exec_step_state p (bir_exec_infinite_steps_fun p st n)))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def, arithmeticTheory.FUNPOW_0,
  arithmeticTheory.FUNPOW_SUC]);


val bir_exec_infinite_steps_fun_ADD = store_thm ("bir_exec_infinite_steps_fun_ADD",
  ``!p st n1 n2. (bir_exec_infinite_steps_fun p (bir_exec_infinite_steps_fun p st n1) n2) =
                 bir_exec_infinite_steps_fun p st (n1 + n2)``,

Induct_on `n1` >> (
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS, arithmeticTheory.ADD_CLAUSES]
));


val bir_exec_step_REWR_TERMINATED = store_thm ("bir_exec_step_REWR_TERMINATED",
  ``!p st.
   bir_state_is_terminated st ==>
   (bir_exec_step p st = (NONE, st))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_exec_step_def]);


val bir_exec_infinite_steps_fun_TERMINATED_0 = store_thm ("bir_exec_infinite_steps_fun_TERMINATED_0",
  ``!p st. bir_state_is_terminated st ==>
           (bir_exec_infinite_steps_fun p st = K st)``,

SIMP_TAC std_ss [FUN_EQ_THM] >>
REPEAT STRIP_TAC >>
rename1 `bir_exec_infinite_steps_fun p st n = _` >>
Induct_on `n` >> (
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS, bir_exec_step_state_def,
    bir_exec_step_REWR_TERMINATED]
));


val bir_exec_infinite_steps_fun_TERMINATED = store_thm ("bir_exec_infinite_steps_fun_TERMINATED",
  ``!p st n1. bir_state_is_terminated (bir_exec_infinite_steps_fun p st n1) ==>
                 (!n2. (n1 <= n2) ==> (bir_exec_infinite_steps_fun p st n2 =
                                       bir_exec_infinite_steps_fun p st n1))``,

REPEAT STRIP_TAC >>
`?c. n2 = n1 + c` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
ASM_SIMP_TAC std_ss [GSYM bir_exec_infinite_steps_fun_ADD,
  bir_exec_infinite_steps_fun_TERMINATED_0]);


val bir_exec_infinite_steps_fun_valid_pc = store_thm ("bir_exec_infinite_steps_fun_valid_pc",
``!p st n. bir_is_valid_pc p (bir_exec_infinite_steps_fun p st n).bst_pc <=>
           bir_is_valid_pc p st.bst_pc``,

Induct_on `n` >> REWRITE_TAC[bir_exec_infinite_steps_fun_REWRS2] >>
ASM_SIMP_TAC std_ss [bir_exec_step_valid_pc]);


(*****************************************)
(* bir_exec_infinite_steps_fun_COUNT_PCs *)
(*****************************************)

val bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF = store_thm ("bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF",
 ``(!pc_cond p st.
      bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st 0 = 0) /\
   (!pc_cond p st n.
     bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st (SUC n) =
     (let r =
            bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p
              st n
      in
        if bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p st (SUC n)) then SUC r
        else r))``,

CONJ_TAC >- REWRITE_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
GEN_TAC >> GEN_TAC >> Induct_on `n` >- (
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_DEF,
    bir_exec_infinite_steps_fun_REWRS]
) >>
ONCE_REWRITE_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_def, bir_programTheory.bir_exec_infinite_steps_fun_REWRS] >>
ASM_SIMP_TAC std_ss [LET_DEF] >>
METIS_TAC[]);


val bir_exec_infinite_steps_fun_COUNT_PCs_ADD = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_ADD",
 ``!pc_cond p st n1 n2.
      bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st (n1 + n2) =
      (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st n1 +
       bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p (bir_exec_infinite_steps_fun p st n1) n2)``,

Induct_on `n2` >> (
  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF,
    arithmeticTheory.ADD_CLAUSES, LET_DEF,
    bir_exec_infinite_steps_fun_ADD]
));


val bir_exec_infinite_steps_fun_PC_COND_SET_def = Define
  `bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p state =
   {i | i <> 0 /\ bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p state i)}`;

val IN_bir_exec_infinite_steps_fun_PC_COND_SET = store_thm (
  "IN_bir_exec_infinite_steps_fun_PC_COND_SET",

``!i pc_cond p st. i IN (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st) <=>
   (i <> 0) /\ (bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p st i))``,

SIMP_TAC (std_ss) [bir_exec_infinite_steps_fun_PC_COND_SET_def,
  GSPECIFICATION]);


val INTER_INSERT_aux = prove (``(s1 INTER (e INSERT s2)) =
  if (e IN s1) then e INSERT (s1 INTER s2) else (s1 INTER s2)``,
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [EXTENSION,
  IN_INTER, IN_INSERT] >>
METIS_TAC[]);


val bir_exec_infinite_steps_fun_COUNT_PCs_ALT_DEF = store_thm (
 "bir_exec_infinite_steps_fun_COUNT_PCs_ALT_DEF",
``!pc_cond p i state. bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i =
  CARD ((bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p state) INTER
        (count (SUC i)))``,

GEN_TAC >> GEN_TAC >>
Induct >- (
  REWRITE_TAC[COUNT_SUC, INTER_INSERT_aux] >>
  SIMP_TAC std_ss [INTER_EMPTY,
    CARD_EMPTY, bir_exec_infinite_steps_fun_COUNT_PCs_def, COUNT_ZERO,
      IN_bir_exec_infinite_steps_fun_PC_COND_SET]
) >>
GEN_TAC >>
ONCE_REWRITE_TAC[COUNT_SUC] >>
ASM_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF,
  INTER_INSERT_aux, IN_bir_exec_infinite_steps_fun_PC_COND_SET] >>
CASE_TAC >>
SIMP_TAC std_ss [CARD_INSERT, FINITE_INTER, FINITE_COUNT,
  IN_INTER, IN_COUNT]);


val bir_pc_cond_impl_def = Define `
  bir_pc_cond_impl (cf1, pc_cond1) (cf2, pc_cond2) <=> (
    (cf1 ==> cf2) /\
    (!pc. pc_cond1 pc ==> pc_cond2 pc))`;


val bir_state_COUNT_PC_MONO = store_thm (
 "bir_state_COUNT_PC_MONO",
``!pc_cond pc_cond'.
   (bir_pc_cond_impl pc_cond pc_cond') ==>
   (!st. bir_state_COUNT_PC pc_cond st ==> bir_state_COUNT_PC pc_cond' st)``,

NTAC 2 Cases >>
STRIP_TAC >> GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def, bir_pc_cond_impl_def] >>
Cases_on `st.bst_status` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
));


val bir_exec_infinite_steps_fun_COUNT_PCs_MONO_PC_COND = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_MONO_PC_COND",
``!pc_cond pc_cond' p state i.
   (bir_pc_cond_impl pc_cond pc_cond') ==>
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i <=
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p state i``,

REPEAT STRIP_TAC >>
Induct_on `i` >- (
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def]
) >>
ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF] >>
Q.ABBREV_TAC `st' = (bir_exec_infinite_steps_fun p state (SUC i))` >>
Cases_on `bir_state_COUNT_PC pc_cond st'` >- (
  `bir_state_COUNT_PC pc_cond' st'` by METIS_TAC[bir_state_COUNT_PC_MONO] >>
  ASM_SIMP_TAC std_ss []
) >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []);


val bir_exec_infinite_steps_fun_COUNT_PCs_LESS_EQ = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_LESS_EQ",
``!pc_cond p state i.
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i <= i``,

GEN_TAC >> GEN_TAC >>
Induct_on `i` >> (
  ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_DEF]
) >>
METIS_TAC[arithmeticTheory.LESS_EQ_SUC_REFL, arithmeticTheory.LESS_EQ_TRANS]);


val bir_exec_infinite_steps_fun_COUNT_PCs_EQ = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_EQ",
``!pc_cond p state i.

   (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i = i) <=> (
   !j. j < i ==> bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p state (SUC j)))``,

GEN_TAC >> GEN_TAC >>
Induct_on `i` >> (
  ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [
    bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF, prim_recTheory.LESS_THM,
    DISJ_IMP_THM, FORALL_AND_THM]
) >>
GEN_TAC >>
DISJ2_TAC >>
`~(SUC i <= i)` by DECIDE_TAC >>
METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_LESS_EQ]);


val bir_state_COUNT_PC_ALL_STEPS = store_thm ("bir_state_COUNT_PC_ALL_STEPS",
  ``!st. bir_state_COUNT_PC (T, \_. T) st``,

GEN_TAC >>
Cases_on `st.bst_status` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_COUNT_PC_def]
));


val bir_exec_infinite_steps_fun_COUNT_PCs_EQ_COUNT_ALL_STEPS = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_EQ_COUNT_ALL_STEPS",
``!p state i.
   (bir_exec_infinite_steps_fun_COUNT_PCs (T, \_. T) p state i = i)``,
SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_EQ,
  bir_state_COUNT_PC_ALL_STEPS]);


val bir_exec_infinite_steps_fun_COUNT_PCs_MONO = store_thm ("bir_exec_infinite_steps_fun_COUNT_PCs_MONO",

``!pc_cond p state i j.
   i <= j ==>
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i <=
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state j``,

SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_DEF] >>
REPEAT STRIP_TAC >>
IRULE_TAC CARD_SUBSET >- (
  SIMP_TAC std_ss [FINITE_INTER, FINITE_COUNT]
) >>
ASM_SIMP_TAC arith_ss [SUBSET_DEF, IN_INTER, IN_COUNT]);



val bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE",
``!pc_cond p state i c_j.
   (c_j < bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i) ==>
   (?j. j < i /\ (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state j = c_j))``,

REPEAT GEN_TAC >>
Induct_on `i` >- (
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def]
) >>
ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF] >>
STRIP_TAC >>
Cases_on `c_j < bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i` >- (
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `j` >>
  ASM_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [] >>
Q.EXISTS_TAC `i` >>
ASM_SIMP_TAC arith_ss []);


val bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ",
``!pc_cond p state i c_j.
   (c_j <= bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i) ==>
   (?j. j <= i /\ (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state j = c_j))``,

METIS_TAC[arithmeticTheory.LESS_OR_EQ,
  bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE]);


val bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_FORALL_NEQ = store_thm (
 "bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_FORALL_NEQ",
``(!i. (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i <> n)) <=>
  (!i. (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i < n))``,

Tactical.REVERSE EQ_TAC >- (
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `!i. _` (MP_TAC o Q.SPEC `i`) >>
  ASM_SIMP_TAC std_ss []
) >- (
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  METIS_TAC[arithmeticTheory.NOT_LESS, bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ]
));


val bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0 = store_thm (
"bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0",
``!pc_cond p state i.

   (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i = 0) <=> (
   !j. j < i ==> ~(bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p state (SUC j))))``,

GEN_TAC >> GEN_TAC >>
Induct_on `i` >> (
  ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [
    bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF, prim_recTheory.LESS_THM,
    DISJ_IMP_THM, FORALL_AND_THM]
));



val FINITE_bir_exec_infinite_steps_fun_PC_COND_SET = store_thm (
"FINITE_bir_exec_infinite_steps_fun_PC_COND_SET",
``!pc_cond p st c.
  (FINITE (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st) /\
   CARD (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st) < c) <=>
  (!i. bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i < c)``,

REPEAT STRIP_TAC >>
Q.ABBREV_TAC `CS = bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st` >>
EQ_TAC >| [
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_DEF] >>
  REPEAT STRIP_TAC >>
  `CARD (CS INTER (count (SUC i))) <= CARD CS` by
    METIS_TAC[CARD_SUBSET, INTER_SUBSET] >>
  DECIDE_TAC,

  STRIP_TAC >>
  CCONTR_TAC >>
  `?s. FINITE s /\ (c <= CARD s) /\ s SUBSET CS` by (
     Cases_on `FINITE CS` >| [
       Q.EXISTS_TAC `CS` >>
       FULL_SIMP_TAC arith_ss [SUBSET_REFL],

       METIS_TAC[INFINITE_SUBSET_WITH_CARD_EXISTS, arithmeticTheory.LESS_EQ_REFL]
     ]
  ) >>
  Q.PAT_X_ASSUM `~(_ /\ _)` (K ALL_TAC) >>

  `?i. c <= bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i` suffices_by
     METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
       arithmeticTheory.NOT_LESS] >>
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_DEF] >>
  Q.EXISTS_TAC `MAX_SET s` >>
  `s SUBSET (CS INTER count (SUC (MAX_SET s)))` suffices_by
      METIS_TAC[CARD_SUBSET, FINITE_INTER, FINITE_COUNT, arithmeticTheory.LESS_EQ_TRANS] >>
  FULL_SIMP_TAC arith_ss [SUBSET_DEF, IN_INTER, IN_COUNT, in_max_set,
     GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC]
]);


val INFINITE_bir_exec_infinite_steps_fun_PC_COND_SET = store_thm (
"INFINITE_bir_exec_infinite_steps_fun_PC_COND_SET",
``!pc_cond p st.
  INFINITE (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st) <=>
  (!c_i. ?i. bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i = c_i)``,

METIS_TAC[FINITE_bir_exec_infinite_steps_fun_PC_COND_SET, prim_recTheory.LESS_SUC_REFL,
   bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_FORALL_NEQ]);



(* If we do not terminate, for most used pc_conds the PC_COND_SET is actually infinite.
   The most important special case is that we count every beginning of blocks. Since
   all blocks are finite, we can only loop, if we execute infinitely many blocks. *)

val bir_exec_infinite_steps_fun_block_starts_at_front = store_thm (
  "bir_exec_infinite_steps_fun_block_starts_at_front",
``!p st n st_n i.
     (st_n = bir_exec_infinite_steps_fun p st n) ==>
     ((bir_exec_infinite_steps_fun p st n).bst_pc.bpc_index = i) ==>
     ~(bir_state_is_terminated st_n) ==>
     (i <= n) ==>

     ((bir_exec_infinite_steps_fun p st (n-i)).bst_pc =
      (st_n.bst_pc with bpc_index := 0))``,

GEN_TAC >> GEN_TAC >>
Induct_on `i` >- (
  SIMP_TAC (std_ss++bir_TYPES_ss) [bir_programTheory.bir_programcounter_t_component_equality]
) >>

FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
Cases_on `n` >> FULL_SIMP_TAC std_ss [] >>
rename1 `i <= n'` >>
Q.ABBREV_TAC `st_n' = (bir_exec_infinite_steps_fun p st n')` >>
Q.PAT_X_ASSUM `!n'. _` (MP_TAC o Q.SPEC `n'`) >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2] >>

Cases_on `bir_state_is_terminated st_n'` >- (
  FULL_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_step_def]
) >>

Tactical.REVERSE (Cases_on `bir_is_valid_pc p st_n'.bst_pc`) >- (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_state_def, bir_exec_step_def,
    GSYM bir_get_current_statement_IS_SOME, bir_state_set_failed_def,
    bir_state_is_terminated_def]
) >>
MP_TAC (Q.SPECL [`p`, `st_n'`] bir_exec_step_state_valid_THM) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>
Tactical.REVERSE (Cases_on `stmt`) >- (
  FULL_SIMP_TAC arith_ss [bir_exec_stmt_state_REWRS, bir_exec_stmtE_block_pc]
) >>

FULL_SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, LET_DEF] >>
Cases_on `bir_state_is_terminated (bir_exec_stmtB_state b st_n')` >> (
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_pc_next_def,
  bir_exec_stmtB_pc_unchanged]);



val bir_is_valid_pc_FINITE = store_thm ("bir_is_valid_pc_FINITE",
``!p. FINITE {pc | bir_is_valid_pc p pc}``,

Cases >> rename1 `BirProgram p` >>
Q.ABBREV_TAC `pcs_of_block = \bl. IMAGE (\i. <| bpc_label := bl.bb_label; bpc_index := i |>)
    (count (SUC (LENGTH bl.bb_statements)))` >>

`{pc | bir_is_valid_pc (BirProgram p) pc} SUBSET (BIGUNION (IMAGE pcs_of_block (set p)))` by (
   Q.UNABBREV_TAC `pcs_of_block` >>
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGUNION, IN_IMAGE,
     PULL_EXISTS, IN_COUNT, bir_is_valid_pc_def] >>
   Cases >>
   SIMP_TAC (std_ss++bir_TYPES_ss) [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
      bir_programcounter_t_component_equality] >>
   REPEAT STRIP_TAC >>
   Q.EXISTS_TAC `bl` >>
   rename1 `bir_get_program_block_info_by_label _ l = _` >>
   FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_def,
     INDEX_FIND_EQ_SOME_0] >>
   METIS_TAC [listTheory.MEM_EL]
) >>

`FINITE (BIGUNION (IMAGE pcs_of_block (set p)))` suffices_by
  METIS_TAC [SUBSET_FINITE] >>

Q.UNABBREV_TAC `pcs_of_block` >>
REPEAT (POP_ASSUM (K ALL_TAC)) >>
MATCH_MP_TAC FINITE_BIGUNION >>
SIMP_TAC std_ss [IN_IMAGE, IMAGE_FINITE, FINITE_COUNT,
  listTheory.FINITE_LIST_TO_SET, PULL_EXISTS]);



(* If we loop a block that is entered infinitely often exists *)
val bir_exec_infinite_steps_fun_LOOPING_BLOCK_EXISTS = store_thm (
"bir_exec_infinite_steps_fun_LOOPING_BLOCK_EXISTS",
``!p st.
   (!n. ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p st n))) ==>
   ?l. MEM l (bir_labels_of_program p) /\
       INFINITE {i | (bir_exec_infinite_steps_fun p st i).bst_pc = bir_block_pc l}``,

REPEAT STRIP_TAC >>
`!n. bir_is_valid_pc p (bir_exec_infinite_steps_fun p st n).bst_pc` by (
   ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_valid_pc] >>
   CCONTR_TAC >>
   `~(bir_state_is_terminated st)` by METIS_TAC[bir_exec_infinite_steps_fun_REWRS] >>
   `bir_state_is_terminated (bir_exec_infinite_steps_fun p st (SUC 0))` suffices_by METIS_TAC[] >>
   SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
   FULL_SIMP_TAC std_ss [
     bir_exec_step_state_def, bir_exec_step_def, GSYM bir_get_current_statement_IS_SOME] >>
   SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
) >>

Q.ABBREV_TAC `index_set_of_pc = \pc. {i | (bir_exec_infinite_steps_fun p st i).bst_pc = pc}` >>

`?pc. bir_is_valid_pc p pc /\ INFINITE (index_set_of_pc pc)` by (
  CCONTR_TAC >>
  `UNIV SUBSET (BIGUNION (IMAGE index_set_of_pc {pc | bir_is_valid_pc p pc}))` by (
     Q.UNABBREV_TAC `index_set_of_pc` >>
     ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNIV, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
       GSPECIFICATION]
  ) >>
  `FINITE (BIGUNION (IMAGE index_set_of_pc {pc | bir_is_valid_pc p pc}))` suffices_by
     METIS_TAC [SUBSET_FINITE, INFINITE_NUM_UNIV] >>

  MATCH_MP_TAC FINITE_BIGUNION >>
  FULL_SIMP_TAC std_ss [IN_IMAGE, PULL_EXISTS, IMAGE_FINITE,
    bir_is_valid_pc_FINITE, GSPECIFICATION] >>
  METIS_TAC[]
) >>


Q.ABBREV_TAC `pc_set = index_set_of_pc pc DIFF (count pc.bpc_index)` >>
`INFINITE pc_set` by METIS_TAC[FINITE_DIFF_down, FINITE_COUNT] >>

Q.PAT_X_ASSUM `INFINITE (index_set_of_pc pc)` (K ALL_TAC) >>
Q.UNABBREV_TAC `index_set_of_pc` >>

`INFINITE (IMAGE (\i. i - pc.bpc_index) pc_set)` by (
  `!x. FINITE {y | x = (\i. i - pc.bpc_index) y}` suffices_by
     METIS_TAC[FINITELY_INJECTIVE_IMAGE_FINITE] >>

  Tactical.REVERSE (Cases_on `x`) >- (
     SIMP_TAC arith_ss [] >>
     rename1 `SUC x' = _` >>
     `{(y:num) | SUC x' = (y - pc.bpc_index)} = {SUC x' + pc.bpc_index}` suffices_by
        SIMP_TAC std_ss [FINITE_SING] >>
     SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION, IN_SING]
  ) >>
  SIMP_TAC arith_ss [] >>
  `{y | y <= pc.bpc_index} = count (SUC pc.bpc_index)` suffices_by SIMP_TAC std_ss [FINITE_COUNT] >>
  SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION, IN_COUNT]
) >>

Q.EXISTS_TAC `pc.bpc_label` >>
ASM_SIMP_TAC std_ss [bir_is_valid_pc_label_OK] >>
`IMAGE (\i. i - pc.bpc_index) pc_set SUBSET
 {(i : num) | (bir_exec_infinite_steps_fun p st i).bst_pc = bir_block_pc pc.bpc_label}`
  suffices_by METIS_TAC[SUBSET_FINITE] >>

Q.UNABBREV_TAC `pc_set` >>
REPEAT (Q.PAT_X_ASSUM `INFINITE _` (K ALL_TAC)) >>

SIMP_TAC arith_ss [SUBSET_DEF, IN_DIFF, IN_COUNT, GSPECIFICATION, bir_block_pc_def,
  IN_IMAGE, PULL_EXISTS] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`, `i`] bir_exec_infinite_steps_fun_block_starts_at_front) >>
ASM_SIMP_TAC arith_ss [] >>

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_programcounter_t_component_equality]);




val bir_exec_infinite_steps_fun_PC_COND_SET_BLOCK_PC = store_thm (
"bir_exec_infinite_steps_fun_PC_COND_SET_BLOCK_PC",
``!p pc_cond st.
   (!pc. (pc.bpc_index = 0) ==> (SND pc_cond) pc) ==>
   (!n. ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p st n))) ==>
   INFINITE (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st)``,

REPEAT GEN_TAC >>
Cases_on `pc_cond` >>
rename1 `SND (cf, pc_cond)` >>
STRIP_TAC >> STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`] bir_exec_infinite_steps_fun_LOOPING_BLOCK_EXISTS) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>

`({i | (bir_exec_infinite_steps_fun p st i).bst_pc = bir_block_pc l} DIFF {0})
 SUBSET (bir_exec_infinite_steps_fun_PC_COND_SET (cf, pc_cond) p st)`
  suffices_by METIS_TAC[SUBSET_FINITE, FINITE_DIFF_down, FINITE_SING] >>

FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [SUBSET_DEF, IN_DIFF, IN_SING, GSPECIFICATION,
  bir_block_pc_def, bir_exec_infinite_steps_fun_PC_COND_SET_def,
  bir_state_COUNT_PC_def, bir_state_is_terminated_def]);




(***************************************)
(* bir_exec_infinite_steps_COUNT_STEPS *)
(***************************************)

val bir_exec_infinite_steps_COUNT_STEPS_UNFOLD = store_thm (
  "bir_exec_infinite_steps_COUNT_STEPS_UNFOLD",
  ``!pc_cond max_steps_opt p st.
    (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st =
     if (bir_state_is_terminated st \/ (max_steps_opt = SOME 0)) then SOME 0 else
     (let st' = bir_exec_step_state p st in
      let max_steps_opt' = if (bir_state_COUNT_PC pc_cond st') then OPT_NUM_PRE max_steps_opt else max_steps_opt in
      OPT_NUM_SUC (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt' p st')))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def,
  whileTheory.OLEAST_def] >>
REPEAT GEN_TAC >>
Q.ABBREV_TAC `P = \max_steps_opt st i.
   (bir_state_is_terminated (bir_exec_infinite_steps_fun p st i) \/
   (max_steps_opt = SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i)))` >>
`(bir_state_is_terminated st \/  (max_steps_opt = SOME 0)) = P max_steps_opt st 0` by (
  Q.UNABBREV_TAC `P` >>
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS,
    bir_exec_infinite_steps_fun_COUNT_PCs_def]
) >>

`!i. ~(P max_steps_opt st 0) ==> (
     (P (if bir_state_COUNT_PC pc_cond  (bir_exec_step_state p st) then OPT_NUM_PRE max_steps_opt
        else max_steps_opt) (bir_exec_step_state p st) i) =
      P max_steps_opt st (SUC i))` by (
  Q.UNABBREV_TAC `P` >>
  FULL_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_infinite_steps_fun_REWRS,
    bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_DEF] >>
  REPEAT STRIP_TAC >>
  Cases_on `max_steps_opt` >> SIMP_TAC std_ss [OPT_NUM_PRE_def] >>
  rename1 `SOME max_steps <> SOME (0:num)` >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `max_steps` >- FULL_SIMP_TAC std_ss [] >>
  rename1 `SUC max_steps' <> (0:num)` >>
  Cases_on `bir_state_COUNT_PC pc_cond (bir_exec_step_state p st)` >> (
    ASM_SIMP_TAC std_ss []
  )
) >>
ASM_SIMP_TAC std_ss [LET_DEF] >>
REPEAT (POP_ASSUM (K ALL_TAC)) >>
Tactical.REVERSE COND_CASES_TAC >- (
  FULL_SIMP_TAC std_ss [OPT_NUM_SUC_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `P max_steps_opt st 0` >- (
  ASM_SIMP_TAC std_ss [] >>
  MATCH_MP_TAC bitTheory.LEAST_THM >>
  ASM_SIMP_TAC std_ss []
) >>
`?i'. i = SUC i'` by (
  Cases_on `i` >> FULL_SIMP_TAC arith_ss []
) >>
BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC (std_ss++QI_ss) [OPT_NUM_SUC_def] >>
MATCH_MP_TAC LEAST_SUC >>
METIS_TAC[]);


val bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWR = store_thm (
  "bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWR",
  ``!pc_cond max_steps p st.
    bir_state_is_terminated st ==>
    (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps p st = SOME 0)``,

SIMP_TAC std_ss [Once bir_exec_infinite_steps_COUNT_STEPS_UNFOLD]);


val bir_exec_infinite_steps_COUNT_STEPS_NO_STEPS_REWR = store_thm (
  "bir_exec_infinite_steps_COUNT_STEPS_NO_STEPS_REWR",
  ``!pc_cond p st.
    (bir_exec_infinite_steps_COUNT_STEPS pc_cond (SOME 0) p st = SOME 0)``,

SIMP_TAC std_ss [Once bir_exec_infinite_steps_COUNT_STEPS_UNFOLD]);


val bir_exec_infinite_steps_COUNT_STEPS_STEP_REWR = store_thm (
 "bir_exec_infinite_steps_COUNT_STEPS_STEP_REWR",
``!pc_cond p st max_steps.
    ~(bir_state_is_terminated st) /\ ~(max_steps = SOME 0) ==>

    (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps p st =
    (let st' = bir_exec_step_state p st in
    let max_steps_opt' =
          if bir_state_COUNT_PC pc_cond st' then OPT_NUM_PRE max_steps
          else max_steps
    in
      OPT_NUM_SUC
        (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt' p
           st')))``,

SIMP_TAC std_ss [Once bir_exec_infinite_steps_COUNT_STEPS_UNFOLD]);


val bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME = store_thm ("bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME",
  ``(bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p state = SOME i) <=>
    ((!n. n < i ==> ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)) /\
                    (max_steps_opt <> SOME
           (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n))) /\
    ((bir_state_is_terminated (bir_exec_infinite_steps_fun p state i)) \/
    (max_steps_opt = SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i))))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_def] >>
Q.ABBREV_TAC `P = (\max_steps_opt state i.
   (bir_state_is_terminated ((bir_exec_infinite_steps_fun p state i))) \/
   (max_steps_opt =
      SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i)))` >>
`!n. (~bir_state_is_terminated (bir_exec_infinite_steps_fun p state n) /\
     (max_steps_opt <> SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n))) =
     ~(P max_steps_opt state n)` by (
  Q.UNABBREV_TAC `P` >> SIMP_TAC std_ss []) >>
ASM_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC) >>
EQ_TAC >> STRIP_TAC >| [
  METIS_TAC[whileTheory.LEAST_EXISTS_IMP],
  METIS_TAC[bitTheory.LEAST_THM]
]);


val bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE = store_thm (
 "bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE",
  ``(bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p state = NONE) <=>
    (!n. ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n))) /\
    (case max_steps_opt of NONE => T | SOME max_steps =>
       (!i. bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i < max_steps))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_def] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [FORALL_AND_THM] >>
STRIP_TAC >>
Cases_on `max_steps_opt` >> SIMP_TAC std_ss [] >>
METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_FORALL_NEQ]);



(***************************************)
(* bir_exec_steps_observe_llist        *)
(***************************************)

val bir_exec_steps_observe_llist_SUC = store_thm ("bir_exec_steps_observe_llist_SUC",
 ``!p st n. bir_exec_steps_observe_llist p st (SOME (SUC n)) =
            (let (fe, st') = bir_exec_step p st in
             let ll' = bir_exec_steps_observe_llist p st' (SOME n) in
             (OPT_LCONS fe ll'))``,

SIMP_TAC arith_ss [bir_exec_steps_observe_llist_NEQ_SOME0, OPT_NUM_PRE_def]);


val bir_exec_steps_observe_llist_NONE = store_thm ("bir_exec_steps_observe_llist_NONE",
 ``!p st. bir_exec_steps_observe_llist p st NONE =
            (let (fe, st') = bir_exec_step p st in
             let ll' = bir_exec_steps_observe_llist p st' NONE in
             (OPT_LCONS fe ll'))``,

SIMP_TAC arith_ss [Once bir_exec_steps_observe_llist_NEQ_SOME0, OPT_NUM_PRE_def]);


val bir_exec_steps_observe_llist_OPT_NUM_SUC = store_thm ("bir_exec_steps_observe_llist_OPT_NUM_SUC",
 ``!p st no.
        bir_exec_steps_observe_llist p st (OPT_NUM_SUC no) =
            (let (fe, st') = bir_exec_step p st in
             let ll' = bir_exec_steps_observe_llist p st' no in
             (OPT_LCONS fe ll'))``,

REPEAT GEN_TAC >>
MP_TAC (Q.SPECL [`p`, `st`, `OPT_NUM_SUC no`] bir_exec_steps_observe_llist_NEQ_SOME0) >>
Cases_on `no` >> SIMP_TAC arith_ss [OPT_NUM_SUC_def, OPT_NUM_PRE_def]);


val bir_exec_steps_observe_llist_REWR_TERMINATED = store_thm ("bir_exec_steps_observe_llist_REWR_TERMINATED",
  ``!p st no.
   bir_state_is_terminated st ==>
   (bir_exec_steps_observe_llist p st no = [||])``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC (std_ss++QI_ss) [bir_exec_steps_observe_llist_def, LMAP_EQ_LNIL,
  LFILTER_EQ_NIL, every_def, llistTheory.exists_LNTH, combinTheory.o_DEF,
  llistTheory.LNTH_LGENLIST, bir_exec_infinite_steps_fun_TERMINATED_0,
  bir_exec_step_REWR_TERMINATED] >>
REPEAT GEN_TAC >> REPEAT CASE_TAC);



(***************************************)
(* bir_exec_steps_observe_list         *)
(***************************************)

(* We often deal with finite sequences of observations. For this
   it is more convenient to work with lists instead of lazy lists.
   Therefore, let's define bir_exec_steps_observe_list
   which corresponds to bir_exec_steps_observe_llist for finite
   sequences of observations. *)

val bir_exec_steps_observe_list_def = Define `
  bir_exec_steps_observe_list p st step_no = (
     MAP THE (FILTER IS_SOME (GENLIST
        (\i. FST (bir_exec_step p (bir_exec_infinite_steps_fun p st i))) step_no)))`;


val bir_exec_steps_observe_list_REWRS = store_thm ("bir_exec_steps_observe_list_REWRS",
 ``(!p st. bir_exec_steps_observe_list p st 0 = []) /\
   (!p st n. bir_exec_steps_observe_list p st (SUC n) =
      let (fe, st') = bir_exec_step p st in
      let l' = bir_exec_steps_observe_list p st' n in
      OPT_CONS fe l')``,

CONJ_TAC >- SIMP_TAC list_ss [bir_exec_steps_observe_list_def] >>
REPEAT GEN_TAC >>
`?fe st'. bir_exec_step p st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [bir_exec_steps_observe_list_def, listTheory.GENLIST_CONS,
  bir_exec_infinite_steps_fun_REWRS, combinTheory.o_DEF, bir_exec_step_state_def, LET_DEF] >>
Cases_on `fe` >> ASM_SIMP_TAC list_ss [OPT_CONS_REWRS]);


val bir_exec_steps_observe_list_ADD = store_thm ("bir_exec_steps_observe_list_ADD",
 ``!p st n1 n2.
      bir_exec_steps_observe_list p st (n1 + n2) =
      (bir_exec_steps_observe_list p st n1 ++
       bir_exec_steps_observe_list p (bir_exec_infinite_steps_fun p st n1) n2)``,

REPEAT GEN_TAC >>
Q.SUBGOAL_THEN `n1 + n2 = n2 + n1` SUBST1_TAC >- DECIDE_TAC >>
SIMP_TAC bool_ss [bir_exec_steps_observe_list_def, listTheory.GENLIST_APPEND] >>
SIMP_TAC list_ss [listTheory.FILTER_APPEND_DISTRIB,
  bir_exec_infinite_steps_fun_ADD] >>
`!i. i + n1 = n1 + i` by DECIDE_TAC >>
ASM_REWRITE_TAC[]);


(***********************************************************************************)
(* connection between bir_exec_steps_observe_llist and bir_exec_steps_observe_list *)
(***********************************************************************************)

val bir_exec_steps_observe_list_fromList = store_thm ("bir_exec_steps_observe_list_fromList",
  ``!p st step_no. (fromList (bir_exec_steps_observe_list p st step_no)) =
                   bir_exec_steps_observe_llist p st (SOME step_no)``,

Induct_on `step_no` >- (
  SIMP_TAC list_ss [bir_exec_steps_observe_llist_0, bir_exec_steps_observe_list_REWRS,
    fromList_def]
) >>
ASM_SIMP_TAC (list_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) [
  bir_exec_steps_observe_llist_SUC, bir_exec_steps_observe_list_REWRS,
  LET_THM, OPT_CONS_fromList]);



val bir_exec_steps_observe_llist_toList_SOME = store_thm ("bir_exec_steps_observe_llist_toList_SOME",
  ``!p st step_no. toList (bir_exec_steps_observe_llist p st (SOME step_no)) =
                   SOME (bir_exec_steps_observe_list p st step_no)``,

METIS_TAC[from_toList, bir_exec_steps_observe_list_fromList]);


val bir_exec_steps_observe_list_to_llist_THE = store_thm ("bir_exec_steps_observe_list_to_llist_THE",
  ``!p st step_no. (bir_exec_steps_observe_list p st step_no) =
                   THE (toList (bir_exec_steps_observe_llist p st (SOME step_no)))``,

SIMP_TAC std_ss [bir_exec_steps_observe_llist_toList_SOME]);



(***************************************************************)
(* properties involving both bir_exec_steps_observe_llist and  *)
(* bir_exec_steps_observe_list                                 *)
(***************************************************************)

val bir_exec_steps_observe_list_REWR_TERMINATED = store_thm ("bir_exec_steps_observe_list_REWR_TERMINATED",
  ``!p st n.
   bir_state_is_terminated st ==>
   (bir_exec_steps_observe_list p st n = [])``,

SIMP_TAC list_ss [bir_exec_steps_observe_list_to_llist_THE,
  bir_exec_steps_observe_llist_REWR_TERMINATED, toList_THM]);



val bir_exec_steps_observe_llist_NONE_ADD = store_thm ("bir_exec_steps_observe_llist_NONE_ADD",
``!p st n. LAPPEND (bir_exec_steps_observe_llist p st (SOME n))
             (bir_exec_steps_observe_llist p (bir_exec_infinite_steps_fun p st n) NONE) =
           bir_exec_steps_observe_llist p st NONE``,

Induct_on `n` >- (
  SIMP_TAC std_ss [bir_exec_steps_observe_llist_0, LAPPEND,
    bir_exec_infinite_steps_fun_REWRS]
) >>
REPEAT GEN_TAC >>
`?fe st'. bir_exec_step p st = (fe,st')` by METIS_TAC[pairTheory.PAIR] >>
CONV_TAC (RHS_CONV (SIMP_CONV std_ss [Once bir_exec_steps_observe_llist_NONE])) >>
ASM_SIMP_TAC std_ss [bir_exec_steps_observe_llist_SUC, LET_THM,
  bir_exec_step_state_def, bir_exec_infinite_steps_fun_REWRS] >>
Cases_on `fe` >> ASM_SIMP_TAC std_ss [LAPPEND, OPT_LCONS_REWRS])


val bir_exec_steps_observe_llist_SOME_ADD = store_thm ("bir_exec_steps_observe_llist_SOME_ADD",
``!p st n1 n2. LAPPEND (bir_exec_steps_observe_llist p st (SOME n1))
             (bir_exec_steps_observe_llist p (bir_exec_infinite_steps_fun p st n1) (SOME n2)) =
           bir_exec_steps_observe_llist p st (SOME (n1 + n2))``,

SIMP_TAC std_ss [GSYM bir_exec_steps_observe_list_fromList, LAPPEND_fromList,
  bir_exec_steps_observe_list_ADD]);


val bir_exec_steps_observe_llist_ADD = store_thm ("bir_exec_steps_observe_llist_ADD",
``!p st n no. LAPPEND (bir_exec_steps_observe_llist p st (SOME n))
             (bir_exec_steps_observe_llist p (bir_exec_infinite_steps_fun p st n) no) =
           bir_exec_steps_observe_llist p st (OPTION_MAP ($+ n) no)``,

Cases_on `no` >> (
  SIMP_TAC std_ss [bir_exec_steps_observe_llist_NONE_ADD,
                   bir_exec_steps_observe_llist_SOME_ADD]
));


val bir_exec_steps_observe_llist_MIN_NUMBER = store_thm ("bir_exec_steps_observe_llist_MIN_NUMBER",
  ``!p st no n. bir_state_is_terminated (bir_exec_infinite_steps_fun p st n) ==>
       (bir_exec_steps_observe_llist p st no =
        bir_exec_steps_observe_llist p st (OPT_NUM_MIN no (SOME n)))``,

REPEAT STRIP_TAC >>
`(OPT_NUM_MIN no (SOME n) = no) \/ (OPT_NUM_MIN no (SOME n) = SOME n)` by METIS_TAC [OPT_NUM_MIN_CASES] >> ASM_REWRITE_TAC[] >>

`(no = NONE) \/ (?c. (no = SOME (n + c)))` by (
   Cases_on `no` >> FULL_SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
   FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.LESS_EQ_EXISTS] >>
   CCONTR_TAC >>
   FULL_SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF]
) >> BasicProvers.VAR_EQ_TAC >> POP_ASSUM (K ALL_TAC) >| [

  (* no = NONE *)
  SUBST1_TAC (Q.SPECL [`p`, `st`, `n`] (GSYM  bir_exec_steps_observe_llist_NONE_ADD)) >>
  ASM_SIMP_TAC std_ss [bir_exec_steps_observe_llist_REWR_TERMINATED,
    LAPPEND_NIL_2ND],


  (* no = SOME ... *)
  ASM_SIMP_TAC bool_ss [GSYM bir_exec_steps_observe_list_fromList,
    bir_exec_steps_observe_list_ADD, bir_exec_steps_observe_list_REWR_TERMINATED,
    listTheory.APPEND_NIL]
]);



val bir_exec_steps_observe_list_MIN_NUMBER = store_thm ("bir_exec_steps_observe_list_MIN_NUMBER",
  ``!p st n1 n2. bir_state_is_terminated (bir_exec_infinite_steps_fun p st n1) ==>
       (bir_exec_steps_observe_list p st n2 =
        bir_exec_steps_observe_list p st (MIN n2 n1))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`, `SOME n2`, `n1`] bir_exec_steps_observe_llist_MIN_NUMBER) >>
ASM_SIMP_TAC std_ss [bir_exec_steps_observe_list_to_llist_THE,
  OPT_NUM_MIN_REWRS]);




(***************************************************************)
(* bir_exec_steps_GEN                                          *)
(***************************************************************)

val bir_exec_steps_GEN_REWR_TERMINATED = store_thm ("bir_exec_steps_GEN_REWR_TERMINATED",
  ``!p st pc_cond max_steps.
    bir_state_is_terminated st ==>
    (bir_exec_steps_GEN pc_cond p st max_steps = BER_Ended [] 0 0 st)``,

SIMP_TAC std_ss [bir_exec_steps_GEN_def,
 bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWR,
  bir_exec_steps_observe_llist_0, LET_DEF,
  bir_exec_infinite_steps_fun_REWRS, toList_THM,
  bir_exec_infinite_steps_fun_COUNT_PCs_def]);


val bir_exec_steps_GEN_REWR_no_steps = store_thm ("bir_exec_steps_GEN_REWR_no_steps",
  ``!pc_cond p st.
    (bir_exec_steps_GEN pc_cond p st (SOME 0) = BER_Ended [] 0 0 st)``,

SIMP_TAC std_ss [bir_exec_steps_GEN_def,
  bir_exec_infinite_steps_COUNT_STEPS_NO_STEPS_REWR,
  bir_exec_steps_observe_llist_0, LET_DEF,
  bir_exec_infinite_steps_fun_REWRS, toList_THM,
  bir_exec_infinite_steps_fun_COUNT_PCs_def]);


val bir_exec_steps_GEN_REWR_STEP = store_thm ("bir_exec_steps_GEN_REWR_STEP",
  ``!pc_cond p st max_steps.
    ~(bir_state_is_terminated st) ==>
    (bir_exec_steps_GEN pc_cond p st max_steps =
      (if (max_steps = SOME 0) then BER_Ended [] 0 0 st else (
      (let (fe, st') = bir_exec_step p st in
       let max_steps' = if (bir_state_COUNT_PC pc_cond st') then (OPT_NUM_PRE max_steps) else max_steps in
       (case (bir_exec_steps_GEN pc_cond p st' max_steps') of
             BER_Ended ol step_count pc_count st_final =>
             BER_Ended (OPT_CONS fe ol) (SUC step_count)
                       (if (bir_state_COUNT_PC pc_cond st') then SUC pc_count else pc_count) st_final
           | BER_Looping oll => BER_Looping (OPT_LCONS fe oll))))))``,

REPEAT GEN_TAC >>
Cases_on `max_steps = SOME 0` >- ASM_SIMP_TAC std_ss [bir_exec_steps_GEN_REWR_no_steps] >>
`?fe st'. bir_exec_step p st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [bir_exec_steps_GEN_def, bir_exec_infinite_steps_COUNT_STEPS_STEP_REWR] >>

ASM_SIMP_TAC std_ss [bir_exec_step_state_def, LET_THM,
  bir_exec_steps_observe_llist_OPT_NUM_SUC] >>
Q.ABBREV_TAC `no = (bir_exec_infinite_steps_COUNT_STEPS pc_cond
         (if bir_state_COUNT_PC pc_cond st' then OPT_NUM_PRE max_steps
          else max_steps) p st')` >>
Cases_on `no` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [OPT_NUM_SUC_def, bir_exec_infinite_steps_fun_REWRS,
    bir_exec_step_state_def]
) >>

ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_THM, bir_exec_step_state_def] >>
Cases_on `fe` >> (
  SIMP_TAC std_ss [bir_exec_steps_observe_llist_toList_SOME, OPT_LCONS_def,
    OPT_CONS_def, toList_THM]
));


val bir_exec_steps_GEN_EQ_Looping = store_thm ("bir_exec_steps_GEN_EQ_Looping",
  ``((bir_exec_steps_GEN pc_cond p state mo) = BER_Looping ll) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (bir_exec_infinite_steps_COUNT_STEPS pc_cond mo p state = NONE))``,

Cases_on `bir_exec_infinite_steps_COUNT_STEPS pc_cond mo p state` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_def, LET_DEF]
));


val num_less_1_eq_0 = prove (``!x: num. (x < 1) <=> (x = 0)``, DECIDE_TAC);


val bir_exec_steps_GEN_1_EQ_Looping = store_thm ("bir_exec_steps_GEN_1_EQ_Looping",
  ``((bir_exec_steps_GEN pc_cond p state (SOME 1)) = BER_Looping ll) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (!n. ~bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)) /\
     (!n. 0 < n ==> ~(bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p state n))))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE, num_less_1_eq_0,
  bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >- (
  GEN_TAC >> STRIP_TAC >>
  Cases_on `n` >> FULL_SIMP_TAC arith_ss [] >>
  METIS_TAC [prim_recTheory.LESS_SUC_REFL]
) >- (
  ASM_SIMP_TAC arith_ss []
));


val bir_exec_steps_GEN_SOME_EQ_Looping = store_thm ("bir_exec_steps_GEN_SOME_EQ_Looping",
  ``((bir_exec_steps_GEN pc_cond p state (SOME step_no)) = BER_Looping ll) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (!n. ~bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)) /\
     (!i. bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state i < step_no))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE]);



(* Together with the theorems about the infinity of
   bir_exec_infinite_steps_fun_PC_COND_SET, we can derive easily, that we
   do terminate, if a step number was given and we count at least when entering a new block. *)

val bir_exec_steps_GEN_NOT_Looping_max_steps_blocks = store_thm (
 "bir_exec_steps_GEN_NOT_Looping_max_steps_blocks",
``!pc_cond p state m.
  (!pc. (pc.bpc_index = 0) ==> (SND pc_cond) pc) ==>
  IS_BER_Ended (bir_exec_steps_GEN pc_cond p state (SOME m))``,

REPEAT STRIP_TAC >>
Cases_on `bir_exec_steps_GEN pc_cond p state (SOME m)` >> (
  SIMP_TAC std_ss [IS_BER_Ended_def]
) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE,
  GSYM FINITE_bir_exec_infinite_steps_fun_PC_COND_SET] >>
METIS_TAC[bir_exec_infinite_steps_fun_PC_COND_SET_BLOCK_PC]);



val bir_exec_steps_GEN_EQ_Ended = store_thm ("bir_exec_steps_GEN_EQ_Ended",
  ``!p state mo ol step_c pc_c state' pc_cond.
    (bir_exec_steps_GEN pc_cond p state mo = BER_Ended ol step_c pc_c state') <=>
    ((ol = bir_exec_steps_observe_list p state step_c) /\
     (pc_c = bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state step_c) /\
     (case mo of NONE => (bir_state_is_terminated state')
               | SOME m => ((pc_c <= m) /\ ((pc_c < m) ==> (bir_state_is_terminated state')) /\
                            (((pc_c = m) /\ (0 < m)) ==> (
                               bir_state_COUNT_PC pc_cond state')))) /\
     (state' = bir_exec_infinite_steps_fun p state step_c) /\
     (!n. n < step_c ==> (~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)) /\
                          mo <> SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n))))``,

REPEAT GEN_TAC >>
EQ_TAC >- (
  SIMP_TAC std_ss [bir_exec_steps_GEN_def, LET_DEF] >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS pc_cond mo p state` >> (
    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
  ) >>
  STRIP_TAC >> REPEAT (BasicProvers.VAR_EQ_TAC) >>
  ASM_SIMP_TAC std_ss [bir_exec_steps_observe_llist_toList_SOME] >>
  Q.PAT_X_ASSUM `_ = SOME step_c` MP_TAC >>
  SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >>
  Q.HO_MATCH_ABBREV_TAC `(_ /\ P step_c mo) ==> _` >>
  REPEAT STRIP_TAC >>
  Cases_on `mo` >- (
    Q.UNABBREV_TAC `P` >>
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [FORALL_AND_THM, IMP_CONJ_THM] >>
  Cases_on `step_c` >- (
    Q.UNABBREV_TAC `P` >>
    FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_def]
  ) >>
  rename1 `P (SUC step_c') (SOME m)` >>
  `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state step_c' < m` by (
     CCONTR_TAC >>
     FULL_SIMP_TAC std_ss [arithmeticTheory.NOT_LESS, GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
     METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ]
  ) >>
  ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF] >>
  Q.UNABBREV_TAC `P` >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF] >>
  Cases_on `bir_state_COUNT_PC pc_cond
          (bir_exec_infinite_steps_fun p state (SUC step_c'))` >> (
    FULL_SIMP_TAC arith_ss []
  )
) >- (
  SIMP_TAC std_ss [bir_exec_steps_GEN_def, LET_DEF] >>
  REPEAT STRIP_TAC >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  Cases_on ` bir_exec_infinite_steps_COUNT_STEPS pc_cond mo p state` >- (
    SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
    Cases_on `mo` >> FULL_SIMP_TAC std_ss [] >>
    rename1 `_ <= (m:num)` >>
    `m = bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state step_c` by DECIDE_TAC >>
    METIS_TAC[FINITE_bir_exec_infinite_steps_fun_PC_COND_SET]
  ) >>
  rename1 `_ = SOME (step_c':num)` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_observe_llist_toList_SOME] >>
  `step_c' = step_c` suffices_by METIS_TAC[] >>
  Q.PAT_X_ASSUM `_ = SOME step_c'` MP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >>
  Q.HO_MATCH_ABBREV_TAC `(_ /\ P step_c' mo) ==> _` >>
  REPEAT STRIP_TAC >>
  Cases_on `mo` >- (
    Q.UNABBREV_TAC `P` >>
    FULL_SIMP_TAC std_ss [] >>
    `~(step_c < step_c')` by METIS_TAC[] >>
    `~(step_c' < step_c)` by METIS_TAC[] >>
    DECIDE_TAC
  ) >>
  rename1 `P _ (SOME m)` >>
  FULL_SIMP_TAC std_ss [] >>
  `~(step_c < step_c')` by (
     CCONTR_TAC >>
     Q.PAT_X_ASSUM `!n. n < step_c' ==> _` (MP_TAC o Q.SPEC `step_c`) >>
     FULL_SIMP_TAC std_ss [] >>
     METIS_TAC [arithmeticTheory.LESS_OR_EQ]
  ) >>
  `~(step_c' < step_c)` by (
     CCONTR_TAC >>
     Q.PAT_X_ASSUM `!n. n < step_c ==> _` (MP_TAC o Q.SPEC `step_c'`) >>
     Q.UNABBREV_TAC `P` >>
     FULL_SIMP_TAC std_ss []
  ) >>
  DECIDE_TAC
));



val bir_exec_steps_GEN_EQ_Ended_0 = store_thm ("bir_exec_steps_GEN_EQ_Ended_0",
  ``(!pc_cond p st max_steps ol c_pc st'.
    (bir_exec_steps_GEN pc_cond p st max_steps = BER_Ended ol 0 c_pc st') <=> (
       (ol = []) /\ (c_pc = 0) /\ (st' = st) /\
       (bir_state_is_terminated st \/ (max_steps = SOME 0))))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Ended,
  bir_exec_infinite_steps_fun_COUNT_PCs_def, bir_exec_steps_observe_list_REWRS,
  bir_exec_infinite_steps_fun_REWRS] >>
Cases_on `max_steps` >> (
  SIMP_TAC std_ss []
) >>
rename1 `0 < m` >>
Cases_on `m` >> SIMP_TAC arith_ss []);



val bir_exec_steps_GEN_EQ_Ended_SUC = store_thm ("bir_exec_steps_GEN_EQ_Ended_SUC",
  ``(!pc_cond p st max_steps c_st ol c_pc st'.
    (bir_exec_steps_GEN pc_cond p st max_steps = BER_Ended ol (SUC c_st) c_pc st') <=> (
       ~(bir_state_is_terminated st) /\ (max_steps <> SOME 0) /\

       let (fe, st1) = bir_exec_step p st in
       let max_steps' = if bir_state_COUNT_PC pc_cond st1 then OPT_NUM_PRE max_steps else max_steps in
       ?ol' c_pc'. (bir_exec_steps_GEN pc_cond p st1 max_steps' = BER_Ended ol' c_st c_pc' st') /\
                   (ol = OPT_CONS fe ol') /\
                   (c_pc = if (bir_state_COUNT_PC pc_cond st1) then SUC c_pc' else c_pc')))``,


REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_TERMINATED]
) >>
Cases_on `max_steps = SOME 0` >- (
  ASM_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_no_steps]
) >>
`?fe st1. bir_exec_step p st = (fe, st1)` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [bir_exec_steps_GEN_REWR_STEP, LET_DEF] >>
Q.ABBREV_TAC `max_steps' = if bir_state_COUNT_PC pc_cond st1 then OPT_NUM_PRE max_steps else max_steps` >>

Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond p st1 max_steps'`) >- (
  SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
SIMP_TAC (std_ss++bir_TYPES_ss++boolSimps.EQUIV_EXTRACT_ss) []);


val bir_exec_steps_GEN_SOME_EQ_Ended = store_thm ("bir_exec_steps_GEN_SOME_EQ_Ended",
  ``!pc_cond p m state mo ol step_c pc_c state'.
    (bir_exec_steps_GEN pc_cond p state (SOME m) = BER_Ended ol step_c pc_c state') <=>
    ((ol = bir_exec_steps_observe_list p state step_c) /\
     (pc_c =
      bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state step_c) /\
     (pc_c <= m /\ (pc_c < m ==> bir_state_is_terminated state') /\
      ((pc_c = m) /\ 0 < m ==> bir_state_COUNT_PC pc_cond state')) /\
     (state' = bir_exec_infinite_steps_fun p state step_c) /\
     (!n.
       n < step_c ==>
       ~bir_state_is_terminated
          (bir_exec_infinite_steps_fun p state n)) /\
     (!n. n < step_c ==>
       bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n < m))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Ended,
  IMP_CONJ_THM, FORALL_AND_THM] >>
REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC >- (
  METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
    arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_LESS_TRANS]
) >- (
  METIS_TAC[prim_recTheory.LESS_REFL]
));


val bir_exec_steps_GEN_1_EQ_Ended = store_thm ("bir_exec_steps_GEN_1_EQ_Ended",
  ``!p state ol step_c pc_c state' pc_cond.
    (bir_exec_steps_GEN pc_cond p state (SOME 1) = BER_Ended ol step_c pc_c state') <=>
    ((ol = bir_exec_steps_observe_list p state step_c) /\
     (if (0 < step_c /\ (bir_state_COUNT_PC pc_cond state')) then
        (pc_c = 1) else (pc_c = 0)) /\
     ((pc_c = 0) ==> (bir_state_is_terminated state')) /\
     (state' = bir_exec_infinite_steps_fun p state step_c) /\
     (!n. n < step_c ==> (~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)))) /\
     (!n. (0 < n /\ n < step_c) ==>
       ~(bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun p state n))))``,


REPEAT GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Ended,
  IMP_CONJ_THM, FORALL_AND_THM] >>
Cases_on `step_c` >- (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [
    bir_exec_infinite_steps_fun_REWRS, bir_exec_infinite_steps_fun_COUNT_PCs_def]
) >>
rename1 `bir_exec_steps_observe_list p state (SUC step_c')` >>
Cases_on `pc_c = 0` >- (
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [
    bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
  REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >- (
    ASM_SIMP_TAC arith_ss [] >>
    Cases >> ASM_SIMP_TAC arith_ss []
  ) >- (
    CONJ_TAC >- (
      GEN_TAC >>
      Cases_on `j = step_c'` >> ASM_SIMP_TAC arith_ss []
    ) >- (
      GEN_TAC >> STRIP_TAC >>
      `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n = 0`
         suffices_by (ASM_SIMP_TAC arith_ss []) >>
      ASM_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0]
    )
  )
) >- (
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `pc_c = 1` >> ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
  REPEAT STRIP_TAC >>
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF,
    bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
  EQ_TAC >> STRIP_TAC >- (
    Cases >> ASM_SIMP_TAC arith_ss []
  ) >- (
    CONJ_TAC >- ASM_SIMP_TAC arith_ss [] >>
    GEN_TAC >> STRIP_TAC >>
    `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p state n = 0` suffices_by
      ASM_SIMP_TAC arith_ss [] >>
    ASM_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0]
  )
));



(***************************************************************)
(* combine multiple runs                                       *)
(***************************************************************)



val bir_exec_steps_GEN_SOME_ADD_Ended = store_thm ("bir_exec_steps_GEN_SOME_ADD_Ended",
  ``!n1 mo pc_count p state0 state1 state2 l1 l2 c_st1 c_st2 c_pc1 c_pc2.
    (bir_exec_steps_GEN pc_count p state0 (SOME n1) = BER_Ended l1 c_pc1 c_st1 state1) ==>
    (bir_exec_steps_GEN pc_count p state1 mo = BER_Ended l2 c_pc2 c_st2 state2) ==>
    (bir_exec_steps_GEN pc_count p state0 (OPTION_MAP (\n2. n1+n2) mo) = BER_Ended (l1++l2)
         (c_pc1+c_pc2) (c_st1 + c_st2) state2)``,

SIMP_TAC arith_ss [bir_exec_steps_GEN_EQ_Ended,
  GSYM bir_exec_steps_observe_list_ADD,
  GSYM bir_exec_infinite_steps_fun_ADD,
  bir_exec_infinite_steps_fun_COUNT_PCs_ADD] >>
REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `st1 = (bir_exec_infinite_steps_fun p state0 c_pc1)` >>
Cases_on ` bir_exec_infinite_steps_fun_COUNT_PCs pc_count p state0 c_pc1 < n1` >- (
  FULL_SIMP_TAC std_ss [] >>
  Q.PAT_X_ASSUM `bir_state_is_terminated _` ASSUME_TAC >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_TERMINATED_0,
    arithmeticTheory.NOT_LESS] >>
  Tactical.REVERSE (Cases_on `c_pc2`) >- METIS_TAC[arithmeticTheory.NOT_SUC_LESS_EQ_0] >>
  FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
  Tactical.REVERSE CONJ_TAC >- (
    REPEAT STRIP_TAC >>
    DISJ2_TAC >>
    `n1 <= n1 + n2` by DECIDE_TAC >>
    METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
      arithmeticTheory.LESS_EQ_LESS_TRANS]
  ) >>
  Cases_on `mo` >> FULL_SIMP_TAC arith_ss []
) >>
`bir_exec_infinite_steps_fun_COUNT_PCs pc_count p state0 c_pc1 = n1` by DECIDE_TAC >>
FULL_SIMP_TAC arith_ss [GSYM bir_exec_infinite_steps_fun_ADD] >>
Tactical.REVERSE CONJ_TAC >- (
  GEN_TAC >> STRIP_TAC >>
  rename1 `(n:num) < c_pc1 + _` >>
  Cases_on `n < c_pc1` >- (
    ASM_SIMP_TAC std_ss [] >>
    GEN_TAC >> DISJ2_TAC >>
    rename1 `_ <> (n1:num) + n2` >>
    `n1 <= n1 + n2` by DECIDE_TAC >>
    METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
      arithmeticTheory.LESS_EQ_LESS_TRANS]
  ) >>
  `?n'. n = c_pc1 + n'` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS, arithmeticTheory.NOT_LESS] >>
  FULL_SIMP_TAC arith_ss [GSYM bir_exec_infinite_steps_fun_ADD,
    bir_exec_infinite_steps_fun_COUNT_PCs_ADD]
) >>
Cases_on `mo` >> (
  FULL_SIMP_TAC std_ss []
) >>
rename1 `0 < n1 + n2` >>
Cases_on `n2 = 0` >- (
  `c_pc2 = 0` by (
     Q.PAT_X_ASSUM `!n. n < c_pc2 ==> _` (MP_TAC o Q.SPEC `0`) >>
     ASM_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def]
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>
FULL_SIMP_TAC arith_ss []);


val bir_exec_steps_GEN_SOME_ADD_Looping = store_thm ("bir_exec_steps_GEN_SOME_ADD_Looping",
  ``!n1 mo pc_count p state0 state1 l1 ll2 c_st1 c_pc1.
    (bir_exec_steps_GEN pc_count p state0 (SOME n1) = BER_Ended l1 c_pc1 c_st1 state1) ==>
    (bir_exec_steps_GEN pc_count p state1 mo = BER_Looping ll2) ==>
    (bir_exec_steps_GEN pc_count p state0 (OPTION_MAP (\n2. n1+n2) mo) = BER_Looping
         (LAPPEND (fromList l1) ll2))``,

SIMP_TAC arith_ss [bir_exec_steps_GEN_EQ_Ended,
  bir_exec_steps_GEN_EQ_Looping] >>
REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
FULL_SIMP_TAC arith_ss [bir_exec_steps_observe_llist_NONE_ADD,
  bir_exec_steps_observe_list_fromList,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE, bir_exec_infinite_steps_fun_ADD] >>
CONJ_TAC >- (
  GEN_TAC >>
  Cases_on `n < c_pc1` >- ASM_SIMP_TAC std_ss [] >>
  METIS_TAC[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_EXISTS]
) >>
Cases_on `mo` >> FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
rename1 `bir_exec_infinite_steps_fun_COUNT_PCs _ _ _ i < n1 + n2` >>
`n2 <> 0` by (
  CCONTR_TAC >>
  FULL_SIMP_TAC arith_ss []
) >>
Cases_on `i <= c_pc1` >- (
  `bir_exec_infinite_steps_fun_COUNT_PCs pc_count p state0 i <= n1` by
    METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_MONO,
      arithmeticTheory.LESS_EQ_TRANS] >>
  DECIDE_TAC
) >>
`c_pc1 <= i` by DECIDE_TAC >>
`?i'. i = c_pc1 + i'` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_ADD] >>
Q.PAT_X_ASSUM `!i. _ < n2` (ASSUME_TAC o Q.SPEC `i'`) >>
DECIDE_TAC);


val bir_exec_steps_GEN_combine = store_thm ("bir_exec_steps_GEN_combine",
  ``!pc_cond p st mo n.

    (!m. (mo = SOME m) ==> n <= m) ==>

    (bir_exec_steps_GEN pc_cond p st mo =
      case (bir_exec_steps_GEN pc_cond p st (SOME n)) of
        BER_Looping ll1 => BER_Looping ll1
      | BER_Ended l1 c1 c1' st1 =>
         (case bir_exec_steps_GEN pc_cond p st1 (OPTION_MAP (\m. m - n) mo) of
           BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
         | BER_Ended l2 c2 c2' st2 =>
           BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2))``,


REPEAT STRIP_TAC >>
Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond p st (SOME n)`) >- (
  rename1 `_ = BER_Looping ll1` >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
  FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Looping,
    bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
  Cases_on `mo` >> FULL_SIMP_TAC std_ss [] >>
  GEN_TAC >>
  `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st i < n` by METIS_TAC[] >>
  DECIDE_TAC
) >>

rename1 `_ = BER_Ended l1 c1 c1' st1` >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
Q.ABBREV_TAC `mo' = OPTION_MAP (\m. m - n) mo` >>

MP_TAC (Q.SPECL [`n`, `mo'`, `pc_cond`, `p`, `st`] bir_exec_steps_GEN_SOME_ADD_Looping) >>
MP_TAC (Q.SPECL [`n`, `mo'`, `pc_cond`, `p`, `st`] bir_exec_steps_GEN_SOME_ADD_Ended) >>

ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>

Q.SUBGOAL_THEN `(OPTION_MAP (\n2. n + n2) mo') = mo` SUBST1_TAC >- (
  Q.UNABBREV_TAC `mo'` >>
  Cases_on `mo` >> (
    FULL_SIMP_TAC arith_ss []
  )
) >>

Cases_on `bir_exec_steps_GEN pc_cond p st1 mo'` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
));


val bir_exec_steps_GEN_REWR_BIG_STEP = store_thm ("bir_exec_steps_GEN_REWR_BIG_STEP",
  ``!pc_cond p st mo.

    (mo <> SOME 0) ==>

    (bir_exec_steps_GEN pc_cond p st mo =
      case (bir_exec_steps_GEN pc_cond p st (SOME 1)) of
        BER_Looping ll1 => BER_Looping ll1
      | BER_Ended l1 c1 c1' st1 =>
         (case bir_exec_steps_GEN pc_cond p st1 (OPT_NUM_PRE mo) of
           BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
         | BER_Ended l2 c2 c2' st2 =>
           BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2))``,


REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`pc_cond`, `p`, `st`, `mo`, `1`] bir_exec_steps_GEN_combine) >>
`(!m. (mo = SOME m) ==> 1 <= m) /\ ((OPTION_MAP (\m. m - 1) mo = OPT_NUM_PRE mo))` by (
  Cases_on `mo` >> FULL_SIMP_TAC arith_ss [OPT_NUM_PRE_def]
) >>
ASM_SIMP_TAC std_ss []);




val bir_exec_steps_GEN_1_step_weaker_cond_1 = store_thm ("bir_exec_steps_GEN_1_step_weaker_cond_1",
  ``!pc_cond pc_cond' p st.
    bir_pc_cond_impl pc_cond pc_cond' ==>
    (bir_exec_steps_GEN pc_cond p st (SOME 1) =
      case (bir_exec_steps_GEN pc_cond' p st (SOME 1)) of
        BER_Looping ll1 => BER_Looping ll1
      | BER_Ended l1 c1 c1' st1 =>
         if (0 < c1) /\ (bir_state_COUNT_PC pc_cond st1) then
           BER_Ended l1 c1 1 st1
         else
         (case bir_exec_steps_GEN pc_cond p st1 (SOME 1) of
           BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
         | BER_Ended l2 c2 c2' st2 =>
           BER_Ended (l1++l2) (c1 + c2) c2' st2))``,


REPEAT STRIP_TAC >>
`!st. bir_state_COUNT_PC pc_cond st ==> bir_state_COUNT_PC pc_cond' st` by
  METIS_TAC [bir_state_COUNT_PC_MONO] >>
Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond' p st (SOME 1)`) >- (
  rename1 `_ = BER_Looping ll1` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_GEN_1_EQ_Looping] >>
  METIS_TAC[]
) >>
rename1 `_ = BER_Ended l1 c1 c1' st1` >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
Q.ABBREV_TAC `cpc = \n. bir_state_COUNT_PC pc_cond
    (bir_exec_infinite_steps_fun p st n)` >>
Q.SUBGOAL_THEN `bir_state_COUNT_PC pc_cond st1 = cpc c1` SUBST1_TAC >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended]
) >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_TERMINATED] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_TERMINATED]
) >>
`0 < c1` by (
  CCONTR_TAC >>
  `c1 = 0` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_0]
) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_1_EQ_Ended] >>

Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond p st (SOME 1)`) >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_1_EQ_Looping] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  `bir_exec_steps_GEN pc_cond p (bir_exec_infinite_steps_fun p st c1) (SOME 1) =
   BER_Looping (bir_exec_steps_observe_llist p (bir_exec_infinite_steps_fun p st c1)
   NONE)` by (
    ASM_SIMP_TAC arith_ss [bir_exec_steps_GEN_1_EQ_Looping,
      bir_exec_infinite_steps_fun_ADD]
  ) >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [
    bir_exec_steps_observe_list_fromList,
    bir_exec_steps_observe_llist_NONE_ADD]
) >>
rename1 `_ = BER_Ended ol c12 c12' st2` >>

`0 < c12` by (
   CCONTR_TAC >>
   `c12 = 0` by DECIDE_TAC >>
   FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
     bir_exec_to_labels_n_def, bir_exec_steps_GEN_EQ_Ended_0]
) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_1_EQ_Ended] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
REV_FULL_SIMP_TAC std_ss [] >>
`~(c12 < c1)` by METIS_TAC[] >>
Cases_on `cpc c1` >- (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
  `c1 = c12` suffices_by METIS_TAC[] >>
  `~(c1 < c12)` by METIS_TAC[] >>
  DECIDE_TAC
) >>
ASM_SIMP_TAC std_ss [] >>

Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond
  p (bir_exec_infinite_steps_fun p st c1) (SOME 1)`) >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_1_EQ_Looping, bir_exec_infinite_steps_fun_ADD] >>
  REV_FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
  `!n. c1 <= n ==> ~(cpc n)` by  (
     GEN_TAC >> STRIP_TAC >>
     `?i. n = c1 + i` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
     Cases_on `i` >> ASM_SIMP_TAC arith_ss []
  ) >>
  `c1 <= c12` by DECIDE_TAC >>
  METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS]
) >>
rename1 `_ = BER_Ended l2 c2 c2' st2` >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>

Cases_on `c2 = 0` >- (
  FULL_SIMP_TAC list_ss [bir_exec_steps_GEN_EQ_Ended_0] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  `~(c1 < c12)` by METIS_TAC[] >>
  `c12 = c1` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss []
) >>

FULL_SIMP_TAC arith_ss [bir_exec_steps_GEN_1_EQ_Ended,
  bir_exec_infinite_steps_fun_ADD] >>
REV_FULL_SIMP_TAC arith_ss [GSYM bir_exec_steps_observe_list_ADD] >>
`c12 = c1 + c2` suffices_by METIS_TAC[] >>
REPEAT BasicProvers.VAR_EQ_TAC >>

`?i. c12 = c1 + i` by METIS_TAC[
  arithmeticTheory.LESS_EQ_EXISTS, arithmeticTheory.NOT_LESS] >>
FULL_SIMP_TAC arith_ss [] >>
`~(i < c2)` by (
   STRIP_TAC >>
   `~(cpc (c1 + i))` suffices_by METIS_TAC[] >>
   Cases_on `i` >> FULL_SIMP_TAC arith_ss []
) >>
`~(c2 < i)` by (
  STRIP_TAC >>
  `0 < c1 + c2 /\ c1+c2 < c1 + i` by DECIDE_TAC >>
  METIS_TAC[]
) >>
DECIDE_TAC);



val bir_exec_steps_GEN_1_step_weaker_cond = store_thm ("bir_exec_steps_GEN_1_step_weaker_cond",
  ``!pc_cond pc_cond' p st n.
    bir_pc_cond_impl pc_cond pc_cond' ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n) =
      if (n = 0) then BER_Ended [] 0 0 st else
      case (bir_exec_steps_GEN pc_cond' p st (SOME 1)) of
        BER_Looping ll1 => BER_Looping ll1
      | BER_Ended l1 c1 _ st1 =>
         let c1' = if (0 < c1) /\ (bir_state_COUNT_PC pc_cond st1) then 1 else 0 in
         (case bir_exec_steps_GEN pc_cond p st1 (SOME (n - c1')) of
           BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
         | BER_Ended l2 c2 c2' st2 =>
           BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2))``,

REPEAT STRIP_TAC >>
Cases_on `n` >- SIMP_TAC std_ss [bir_exec_steps_GEN_REWR_no_steps] >>
rename1 `SOME (SUC n')` >>
SIMP_TAC arith_ss [Once bir_exec_steps_GEN_REWR_BIG_STEP, OPT_NUM_PRE_def] >>
MP_TAC (Q.SPECL [`pc_cond`, `pc_cond'`, `p`, `st`] bir_exec_steps_GEN_1_step_weaker_cond_1) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>

Tactical.REVERSE (Cases_on `bir_exec_steps_GEN pc_cond' p st (SOME 1)`) >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
rename1 `_ = BER_Ended l1 c1 c1' st1` >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
Q.ABBREV_TAC `cond = 0 < c1 /\ bir_state_COUNT_PC pc_cond st1` >>

Cases_on `cond` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [LET_DEF]
) >>
MP_TAC (Q.SPECL [`pc_cond`, `p`, `st1`, `(SOME (SUC n'))`]
   bir_exec_steps_GEN_REWR_BIG_STEP) >>
ASM_SIMP_TAC arith_ss [OPT_NUM_PRE_def] >>

Cases_on `bir_exec_steps_GEN pc_cond p st1 (SOME 1)` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
rename1 `_ = BER_Ended l1' c1'' c1''' st1'` >>
Cases_on `bir_exec_steps_GEN pc_cond p st1' (SOME n')` >> (
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [GSYM llistTheory.LAPPEND_fromList,
    llistTheory.LAPPEND_ASSOC]
));






(***************************************************************)
(* bir_exec_step_n                                             *)
(***************************************************************)

val bir_exec_step_n_TO_steps_GEN = store_thm ("bir_exec_step_n_TO_steps_GEN",
  ``((bir_exec_step_n p state n = (l, c, state'))) <=>
     (bir_exec_steps_GEN (T, \_. T) p state (SOME n) =
     (BER_Ended l c c state'))``,

`IS_BER_Ended (bir_exec_steps_GEN (T, \_. T) p state (SOME n))` by (
  MATCH_MP_TAC bir_exec_steps_GEN_NOT_Looping_max_steps_blocks >>
  SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_exec_step_n_def, IS_BER_Ended_EXISTS,
  valOf_BER_Ended_steps_def] >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_COUNT_ALL_STEPS,
  bir_exec_steps_GEN_EQ_Ended]);


val bir_exec_step_n_EQ_THM = store_thm ("bir_exec_step_n_EQ_THM",
  ``((bir_exec_step_n p state n = (l, c, state'))) <=>
    ((l = bir_exec_steps_observe_list p state c) /\
     (c <= n) /\ (c < n ==> bir_state_is_terminated state') /\
     (state' = bir_exec_infinite_steps_fun p state c) /\
     (!n.
        n < c ==>
        ~bir_state_is_terminated
           (bir_exec_infinite_steps_fun p state n)))``,

SIMP_TAC std_ss [bir_exec_step_n_TO_steps_GEN] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Ended,
  bir_exec_infinite_steps_fun_COUNT_PCs_EQ_COUNT_ALL_STEPS,
  bir_state_COUNT_PC_ALL_STEPS]);


val bir_exec_step_n_combine = store_thm ("bir_exec_step_n_combine",
  ``!p state0 state1 state2 n1 n2 l1 l2 c1 c2.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_step_n p state1 n2 = (l2, c2, state2)) ==>
    (bir_exec_step_n p state0 (n1 + n2) = (l1++l2, c1+c2, state2))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`n1`, `SOME n2`] bir_exec_steps_GEN_SOME_ADD_Ended) >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_TO_steps_GEN] >>
METIS_TAC[]);


val bir_exec_step_n_add = store_thm ("bir_exec_step_n_add",
  ``!p state0 n1 n2.
    (bir_exec_step_n p state0 (n1 + n2) =
      let (l1, c1, state1) = bir_exec_step_n p state0 n1 in
      let (l2, c2, state2) = bir_exec_step_n p state1 n2 in
      (l1++l2, c1+c2, state2))``,

REPEAT GEN_TAC >>
`?l1 c1 state1. bir_exec_step_n p state0 n1 = (l1, c1, state1)` by METIS_TAC[pairTheory.PAIR] >>
`?l2 c2 state2. bir_exec_step_n p state1 n2 = (l2, c2, state2)` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM] >>
METIS_TAC[bir_exec_step_n_combine]);


val bir_exec_step_n_REWR_0 = store_thm ("bir_exec_step_n_REWR_0",
  ``!p state. bir_exec_step_n p state 0 = ([], 0, state)``,
SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, bir_exec_steps_observe_list_REWRS,
  bir_exec_infinite_steps_fun_REWRS]);


val bir_exec_step_n_REWR_TERMINATED = store_thm ("bir_exec_step_n_REWR_TERMINATED",
  ``!p state n. bir_state_is_terminated state ==> (bir_exec_step_n p state n = ([], 0, state))``,
SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, bir_exec_infinite_steps_fun_REWRS,
  bir_exec_steps_observe_list_REWRS]);


val bir_exec_step_n_REWR_1 = store_thm ("bir_exec_step_n_REWR_1",
  ``!p state. bir_exec_step_n p state 1 =
         (if (bir_state_is_terminated state) then ([], 0, state) else
         (let (fe, st') = bir_exec_step p state in
         ((OPT_CONS fe []), 1, st')))``,

REPEAT STRIP_TAC >>
`?fe st'. bir_exec_step p state = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
Q.SUBGOAL_THEN `1 = SUC 0` SUBST1_TAC >- SIMP_TAC std_ss [] >>
Cases_on `bir_state_is_terminated state` >> (
  ASM_SIMP_TAC (bool_ss++pairSimps.gen_beta_ss) [bir_exec_step_n_EQ_THM,
    bir_exec_steps_observe_list_REWRS, LET_THM] >>
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS, bir_exec_step_state_def]
) >>
REPEAT STRIP_TAC >>
rename1 `n < 1` >>
`n = 0` by DECIDE_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]);


val bir_exec_step_n_SUC = store_thm ("bir_exec_step_n_SUC",
`` !p st n.
   bir_exec_step_n p st (SUC n) =
   if bir_state_is_terminated st then ([],0,st) else
   let (fe,st') = bir_exec_step p st in
   let (l,c,st'') = bir_exec_step_n p st' n in
   (OPT_CONS fe l, SUC c, st'')``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `SUC n = 1 + n` SUBST1_TAC >- DECIDE_TAC >>
ASM_SIMP_TAC bool_ss [bir_exec_step_n_add, bir_exec_step_n_REWR_1] >>
Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC list_ss [LET_THM, bir_exec_step_n_REWR_TERMINATED]
) >>
ASM_SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [LET_THM, OPT_CONS_APPEND]);


val bir_exec_step_n_SUC_END = store_thm ("bir_exec_step_n_SUC_END",
`` !p st n.
   bir_exec_step_n p st (SUC n) =
   let (l,c,st') = bir_exec_step_n p st n in
   if bir_state_is_terminated st' then (l,c,st') else
   let (fe,st'') = bir_exec_step p st' in
   (l ++ OPT_CONS fe [], SUC c, st'')``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `SUC n = n + 1` SUBST1_TAC >- DECIDE_TAC >>
ASM_SIMP_TAC bool_ss [bir_exec_step_n_add, bir_exec_step_n_REWR_1] >>
`?l c st'. bir_exec_step_n p st n = (l, c, st')` by METIS_TAC[pairTheory.PAIR] >>
`?fe st''. bir_exec_step p st' = (fe, st'')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC list_ss [LET_THM] >>
Cases_on `bir_state_is_terminated st'` >> (
  ASM_SIMP_TAC list_ss []
));


val bir_exec_step_n_REWR_NOT_TERMINATED = store_thm ("bir_exec_step_n_REWR_NOT_TERMINATED",
  ``!p st n. ~bir_state_is_terminated st ==>
       (bir_exec_step_n p st (SUC n) =
         (let (fe, st') = bir_exec_step p st in
          let (l, n', st'') = bir_exec_step_n p st' n in
          (OPT_CONS fe l, SUC n', st'')))``,

SIMP_TAC std_ss [bir_exec_step_n_SUC]);


val bir_exec_step_n_REWRS = save_thm ("bir_exec_step_n_REWRS",
  LIST_CONJ [bir_exec_step_n_REWR_0, bir_exec_step_n_REWR_1,
    bir_exec_step_n_REWR_NOT_TERMINATED, bir_exec_step_n_REWR_TERMINATED]);


val bir_exec_step_n_COUNT_0 = store_thm ("bir_exec_step_n_COUNT_0",
  ``!p l state state' c. (bir_exec_step_n p state c = (l, 0, state')) <=>
      ((l = []) /\ (state' = state) /\ (0 < c ==> bir_state_is_terminated state)) ``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_step_n_EQ_THM,
  bir_exec_infinite_steps_fun_REWRS,
  bir_exec_steps_observe_list_REWRS]);



(***************************************************************)
(* bir_exec_block_n                                            *)
(***************************************************************)

val bir_exec_block_n_TO_steps_GEN = store_thm ("bir_exec_block_n_TO_steps_GEN",
  ``((bir_exec_block_n p state n = (l, c_bl, c_st, state'))) <=>
     (bir_exec_steps_GEN (F, \pc. pc.bpc_index = 0) p state (SOME n) =
     (BER_Ended l c_bl c_st state'))``,

`IS_BER_Ended (bir_exec_steps_GEN (F, \pc. pc.bpc_index = 0) p state (SOME n))` by (
  MATCH_MP_TAC bir_exec_steps_GEN_NOT_Looping_max_steps_blocks >>
  SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_exec_block_n_def, IS_BER_Ended_EXISTS,
  valOf_BER_Ended_def]);


val bir_exec_block_n_EQ_THM = store_thm ("bir_exec_block_n_EQ_THM",
  ``((bir_exec_block_n p state n = (l, c_st, c_bl, state'))) <=>

    ((l = bir_exec_steps_observe_list p state c_st) /\
     (c_bl = bir_exec_infinite_steps_fun_COUNT_PCs (F, \pc. pc.bpc_index = 0) p state c_st) /\
     (c_bl <= n) /\ (c_bl < n ==> bir_state_is_terminated state') /\
     (state' = bir_exec_infinite_steps_fun p state c_st) /\
     ((bir_exec_infinite_steps_fun_COUNT_PCs (F, \pc. pc.bpc_index = 0) p state c_st = n) /\
       0 < n ==>
       (bir_state_COUNT_PC (F, \pc. pc.bpc_index = 0) (bir_exec_infinite_steps_fun p state c_st))) /\
       (!n'. n' < c_st ==>
          ~bir_state_is_terminated (bir_exec_infinite_steps_fun p state n') /\
          bir_exec_infinite_steps_fun_COUNT_PCs (F, \pc. pc.bpc_index = 0) p state n' < n))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_block_n_TO_steps_GEN,
  bir_exec_steps_GEN_EQ_Ended, IMP_CONJ_THM, FORALL_AND_THM] >>
REPEAT STRIP_TAC >>
Tactical.REVERSE EQ_TAC >- (
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `!n'. n' < c_st ==> _` (MP_TAC o Q.SPEC `n'`) >>
  FULL_SIMP_TAC arith_ss []
) >>
REPEAT STRIP_TAC >>
CCONTR_TAC >>
FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS] >>
METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
  arithmeticTheory.LESS_EQ_LESS_TRANS]);


val bir_exec_block_n_combine = store_thm ("bir_exec_block_n_combine",
  ``!p state0 state1 state2 n1 n2 l1 l2 c_bl1 c_bl2 c_st1 c_st2.
    (bir_exec_block_n p state0 n1 = (l1, c_bl1, c_st1, state1)) ==>
    (bir_exec_block_n p state1 n2 = (l2, c_bl2, c_st2, state2)) ==>
    (bir_exec_block_n p state0 (n1 + n2) = (l1++l2, c_bl1+c_bl2, c_st1 + c_st2, state2))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`n1`, `SOME n2`, `(F, \pc. pc.bpc_index = 0)`, `p`, `state0`]
  bir_exec_steps_GEN_SOME_ADD_Ended) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_block_n_TO_steps_GEN]);


val bir_exec_block_n_add = store_thm ("bir_exec_block_n_add",
  ``!p state0 n1 n2.
    (bir_exec_block_n p state0 (n1 + n2) =
      let (l1, c_bl1, c_st1, state1) = bir_exec_block_n p state0 n1 in
      let (l2, c_bl2, c_st2, state2) = bir_exec_block_n p state1 n2 in
      (l1++l2, c_bl1+c_bl2, c_st1+c_st2, state2))``,

REPEAT GEN_TAC >>
`?l1 c_bl1 c_st1 state1. bir_exec_block_n p state0 n1 = (l1, c_bl1, c_st1, state1)` by METIS_TAC[pairTheory.PAIR] >>
`?l2 c_bl2 c_st2 state2. bir_exec_block_n p state1 n2 = (l2, c_bl2, c_st2, state2)` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM] >>
METIS_TAC[bir_exec_block_n_combine]);


val bir_exec_block_n_REWR_0 = store_thm ("bir_exec_block_n_REWR_0",
  ``!p state. bir_exec_block_n p state 0 = ([], 0, 0, state)``,
SIMP_TAC std_ss [bir_exec_block_n_def, bir_exec_steps_GEN_REWR_no_steps,
  valOf_BER_Ended_def]);


val bir_exec_block_n_REWR_TERMINATED = store_thm ("bir_exec_block_n_REWR_TERMINATED",
  ``!p state n. bir_state_is_terminated state ==> (bir_exec_block_n p state n = ([], 0, 0, state))``,
SIMP_TAC std_ss [bir_exec_block_n_def, bir_exec_steps_GEN_REWR_TERMINATED,
  valOf_BER_Ended_def]);


(***************************************************************)
(* bir_exec_to_labels_n                                        *)
(***************************************************************)

val bir_exec_block_n_TO_bir_exec_to_labels_n = store_thm ("bir_exec_block_n_TO_bir_exec_to_labels_n",
  ``(bir_exec_block_n p st m = (ol, c_st, c_pc, st')) <=>
    (bir_exec_to_labels_n UNIV p st m = BER_Ended ol c_st c_pc st')``,

SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
  bir_exec_to_labels_n_def, IN_UNIV]);


val bir_exec_to_labels_n_UNIV_REWR = store_thm ("bir_exec_to_labels_n_UNIV_REWR",
  ``bir_exec_to_labels_n UNIV p st m =
    let (ol, c_st, c_pc, st') = bir_exec_block_n p st m in
    BER_Ended ol c_st c_pc st'``,

`?ol c_st c_pc st'. bir_exec_block_n p st m = (ol, c_st, c_pc, st')`
   by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM] >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_bir_exec_to_labels_n]);



val bir_exec_to_labels_n_REWR_0 = store_thm ("bir_exec_to_labels_n_REWR_0",
``!ls p st. bir_exec_to_labels_n ls p st 0 = BER_Ended [] 0 0 st``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_steps_GEN_REWR_no_steps]);


val bir_exec_to_labels_n_REWR_TERMINATED = store_thm ("bir_exec_to_labels_n_REWR_TERMINATED",
``!ls p st n. bir_state_is_terminated st ==> (bir_exec_to_labels_n ls p st n = BER_Ended [] 0 0 st)``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_steps_GEN_REWR_TERMINATED]);


val bir_exec_to_labels_n_REWR_SUC = store_thm ("bir_exec_to_labels_n_REWR_SUC",
``!ls p st n.
    (bir_exec_to_labels_n ls p st (SUC n) =
      case (bir_exec_to_labels ls p st) of
        BER_Looping ll1 => BER_Looping ll1
      | BER_Ended l1 c1 c1' st1 =>
         (case bir_exec_to_labels_n ls p st1 n of
           BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
         | BER_Ended l2 c2 c2' st2 =>
           BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2))``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_to_labels_def] >>
SIMP_TAC arith_ss [Once bir_exec_steps_GEN_REWR_BIG_STEP, OPT_NUM_PRE_def]);



val bir_exec_to_labels_n_block_1 = store_thm ("bir_exec_to_labels_n_block_1",
  ``!ls p st n.

    (bir_exec_to_labels_n ls p st (SUC n) =
      let (l1, c1, _, st1) = bir_exec_block_n p st 1 in
      let c1' = if (0 < c1) /\ (bir_state_COUNT_PC (F,
         \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) st1) then 1 else 0 in
      case bir_exec_to_labels_n ls p st1 (SUC n-c1') of
        BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2)
      | BER_Ended l2 c2 c2' st2 =>
        BER_Ended (l1++l2) (c1 + c2) (c1' + c2') st2)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
MP_TAC (Q.SPECL [`(F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls))`,
                 `(F,(\pc. pc.bpc_index = 0))`, `p`, `st`, `SUC n`]
   bir_exec_steps_GEN_1_step_weaker_cond) >>
ASM_SIMP_TAC arith_ss [bir_pc_cond_impl_def] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
`?l1 c1 c1_aux st1. bir_exec_block_n p st 1 = (l1, c1, c1_aux, st1)` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM] >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_block_n_TO_steps_GEN]);




(***************************************************************)
(* bir_exec_steps                                              *)
(***************************************************************)

val bir_exec_steps_EQ_Looping = store_thm ("bir_exec_steps_EQ_Looping",
  ``(bir_exec_steps p state = BER_Looping ll) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (!n. ~bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE]);


val bir_exec_steps_EQ_Ended = store_thm ("bir_exec_steps_EQ_Ended",
  ``((bir_exec_steps p state = BER_Ended l c1 c2 state') <=>
    ((l = bir_exec_steps_observe_list p state c1) /\
     (c1 = c2) /\
     bir_state_is_terminated state' /\
     (state' = bir_exec_infinite_steps_fun p state c1) /\
     (!n. n < c1 ==> ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)))))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_def, bir_exec_steps_GEN_EQ_Ended,
  bir_exec_infinite_steps_fun_COUNT_PCs_EQ_COUNT_ALL_STEPS]);


val bir_exec_steps_REWR_TERMINATED = store_thm ("bir_exec_steps_REWR_TERMINATED",
  ``bir_state_is_terminated state ==>
    (bir_exec_steps p state = BER_Ended [] 0 0 state)``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_GEN_REWR_TERMINATED]);


val bir_exec_steps_REWR_NOT_TERMINATED = store_thm ("bir_exec_steps_REWR_NOT_TERMINATED",
  ``~bir_state_is_terminated state ==>
    (bir_exec_steps p state =
       let (fe, state') = bir_exec_step p state in
       case bir_exec_steps p state' of
         BER_Ended ol step_count pc_count st_final =>
           BER_Ended (OPT_CONS fe ol) (SUC step_count) (SUC pc_count)
             st_final
         | BER_Looping oll => BER_Looping (OPT_LCONS fe oll))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_GEN_REWR_STEP,
  OPT_NUM_PRE_def, LET_THM, bir_state_COUNT_PC_ALL_STEPS]);


val bir_exec_steps_combine = store_thm ("bir_exec_steps_combine",
  ``!p state0 n1 state1 c1 l1.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_steps p state0 =
       case bir_exec_steps p state1 of
         BER_Ended ol step_count pc_count st_final =>
           BER_Ended (l1 ++ ol) (c1 + step_count) (c1 + pc_count)
             st_final
         | BER_Looping oll => BER_Looping (LAPPEND (fromList l1) oll))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`n1`, `NONE`, `(T, \_. T)`, `p`, `state0`] bir_exec_steps_GEN_SOME_ADD_Ended) >>
MP_TAC (Q.SPECL [`n1`, `NONE`, `(T, \_. T)`, `p`, `state0`] bir_exec_steps_GEN_SOME_ADD_Looping) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_n_TO_steps_GEN, GSYM bir_exec_steps_def] >>

Cases_on `bir_exec_steps p state1` >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
));


val bir_exec_steps_combine_GUARD = store_thm ("bir_exec_steps_combine_GUARD",
  ``!p state0 n1 state1 c1 l1.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_steps p state0 =
       (if c1 < n1 then BER_Ended l1 c1 c1 state1 else (
       case bir_exec_steps p state1 of
         BER_Ended ol step_count pc_count st_final =>
           BER_Ended (l1 ++ ol) (c1 + step_count) (c1 + pc_count)
             st_final
         | BER_Looping oll => BER_Looping (LAPPEND (fromList l1) oll))))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `state0`, `n1`] bir_exec_steps_combine) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `c1 < n1` >> ASM_REWRITE_TAC[] >>
`bir_state_is_terminated state1` by (
   FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM]
) >>
FULL_SIMP_TAC (list_ss++bir_TYPES_ss) [bir_exec_steps_REWR_TERMINATED]);



(***************************************************************)
(* conversions between various instances of bir_exec_steps_GEN *)
(***************************************************************)

(* If we do not terminate, we can increase the max-step-count *)
val bir_exec_steps_GEN_increase_max_steps_looping_SOME = store_thm (
"bir_exec_steps_GEN_increase_max_steps_looping_SOME",
  ``!pc_cond p st ll n1 n2.
    (n1 <= n2) ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Looping ll) ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n2) = BER_Looping ll)``,

SIMP_TAC arith_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!i. _` (MP_TAC o Q.SPEC `i`) >>
ASM_SIMP_TAC arith_ss []);


val bir_exec_steps_GEN_increase_max_steps_looping_NONE = store_thm (
"bir_exec_steps_GEN_increase_max_steps_looping_NONE",
  ``!pc_cond p st ll n.
    (bir_exec_steps_GEN pc_cond p st (SOME n) = BER_Looping ll) ==>
    (bir_exec_steps_GEN pc_cond p st NONE = BER_Looping ll)``,

SIMP_TAC arith_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE]);


val bir_exec_steps_GEN_EQ_Ended_FIX_STEPS = store_thm (
"bir_exec_steps_GEN_EQ_Ended_FIX_STEPS",
  ``!pc_cond p st ol c_pc c_st st' mo.
    ((bir_exec_steps_GEN pc_cond p st mo = BER_Ended ol c_st c_pc st')) ==>
    (bir_exec_steps_GEN pc_cond p st (SOME
       (if (bir_state_COUNT_PC pc_cond st' \/ (mo = SOME 0)) then c_pc else SUC c_pc)) = BER_Ended ol c_st c_pc st')``,

REPEAT STRIP_TAC >>
`(mo = SOME 0) ==> (c_st = 0)` by (
  STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_no_steps] >>
  REPEAT (BasicProvers.VAR_EQ_TAC) >> REWRITE_TAC[]
) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
Q.ABBREV_TAC `cc =  bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st c_st` >>
Q.ABBREV_TAC `st' = bir_exec_infinite_steps_fun p st c_st` >>

Cases_on `bir_state_COUNT_PC pc_cond st'` >- (
   FULL_SIMP_TAC std_ss [] >>
   Q.UNABBREV_TAC `cc` >>
   Q.UNABBREV_TAC `st'` >>
   Cases_on `c_st` >- FULL_SIMP_TAC std_ss [] >>
   FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_THM,
     GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
   GEN_TAC >> STRIP_TAC >>
   rename1 `(na:num) <= nb` >>
   `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st na <=
    bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st nb` by
    METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_MONO] >>
   ASM_SIMP_TAC arith_ss []
) >- (
   Cases_on `mo = SOME 0` >- (
     FULL_SIMP_TAC std_ss []
   ) >>
   CONJ_TAC >- (
     Cases_on `mo` >> FULL_SIMP_TAC arith_ss []
   ) >>
   ASM_SIMP_TAC std_ss [] >>
   REPEAT STRIP_TAC >>
   `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st n <= cc`
      by METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_MONO,
           arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
   FULL_SIMP_TAC arith_ss []
));


val bir_exec_steps_GEN_increase_max_steps_Ended_NONE = store_thm (
"bir_exec_steps_GEN_increase_max_steps_Ended_NONE",
  ``!pc_cond p st ol c_pc c_st st' n.
    (bir_state_is_terminated st') ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n) = BER_Ended ol c_pc c_st st') ==>
    (bir_exec_steps_GEN pc_cond p st NONE = BER_Ended ol c_pc c_st st')``,

SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended]);


val bir_exec_steps_GEN_increase_max_steps_Ended_SOME = store_thm (
"bir_exec_steps_GEN_increase_max_steps_Ended_SOME",
  ``!pc_cond p st ol c_pc c_st st' n1 n2.
    (n1 <= n2) ==>
    (bir_state_is_terminated st') ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Ended ol c_pc c_st st') ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n2) = BER_Ended ol c_pc c_st st')``,

REPEAT STRIP_TAC >>
`?i. n2 = n1 + i` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended] >>
Q.PAT_X_ASSUM `bir_state_is_terminated _` ASSUME_TAC >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>
FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
`n1 <= i + n1` by DECIDE_TAC >>
METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_COMPLETE_LESS_EQ,
      arithmeticTheory.LESS_EQ_LESS_TRANS]);



val bir_exec_steps_GEN_change_cond_Looping_NONE = store_thm (
"bir_exec_steps_GEN_change_cond_Looping_NONE",
  ``!pc_cond pc_cond' mo p st ll.
    (bir_exec_steps_GEN pc_cond p st mo = BER_Looping ll) ==>
    (bir_exec_steps_GEN pc_cond' p st NONE = BER_Looping ll)``,

SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE]);



val bir_exec_steps_GEN_change_cond_Looping_SOME = store_thm (
"bir_exec_steps_GEN_change_cond_Looping_SOME",
  ``!pc_cond pc_cond' p st ll n1.
    (bir_pc_cond_impl pc_cond' pc_cond) ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Looping ll) ==>
    (?n2. (n2 <= n1) /\ ((bir_exec_steps_GEN pc_cond' p st (SOME n2) = BER_Looping ll)))``,

SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE,
  GSYM FINITE_bir_exec_infinite_steps_fun_PC_COND_SET] >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `SUC (CARD (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st))` >>
FULL_SIMP_TAC std_ss [GSYM arithmeticTheory.LESS_EQ,
  GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
`(bir_exec_infinite_steps_fun_PC_COND_SET pc_cond' p st) SUBSET
 (bir_exec_infinite_steps_fun_PC_COND_SET pc_cond p st)` suffices_by
  METIS_TAC[SUBSET_FINITE, CARD_SUBSET] >>
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_bir_exec_infinite_steps_fun_PC_COND_SET] >>
METIS_TAC[bir_state_COUNT_PC_MONO]);



val bir_exec_steps_GEN_change_cond_Ended_terminated = store_thm (
"bir_exec_steps_GEN_change_cond_Ended_terminated",
  ``!pc_cond pc_cond' p st ol c_pc c_st mo st'.
    bir_state_is_terminated st' ==>
    (bir_exec_steps_GEN pc_cond p st mo = BER_Ended ol c_st c_pc st') ==>
    (?c_pc'. bir_exec_steps_GEN pc_cond' p st NONE = BER_Ended ol c_st c_pc' st')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended]);


val bir_exec_steps_GEN_change_cond_Ended_NONE = store_thm (
"bir_exec_steps_GEN_change_cond_Ended_NONE",
  ``!pc_cond pc_cond' p st ol c_pc c_st st'.
    (bir_exec_steps_GEN pc_cond p st NONE = BER_Ended ol c_st c_pc st') ==>
    (?c_pc'. bir_exec_steps_GEN pc_cond' p st NONE = BER_Ended ol c_st c_pc' st')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended]);


val bir_exec_steps_GEN_change_cond_Ended_SOME = store_thm (
"bir_exec_steps_GEN_change_cond_Ended_SOME",
  ``!pc_cond pc_cond' p st n1 ol c_pc c_st st'.
    (bir_pc_cond_impl pc_cond pc_cond') ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Ended ol c_st c_pc st') ==>
    ?n2 c_pc'. (n1 <= n2) /\ (bir_exec_steps_GEN pc_cond' p st (SOME n2) = BER_Ended ol c_st c_pc' st')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended]  >>
REPEAT BasicProvers.VAR_EQ_TAC >>

Q.ABBREV_TAC `cc = bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st c_st` >>
Q.ABBREV_TAC `st' = (bir_exec_infinite_steps_fun p st c_st)` >>
`bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st c_st <= cc` by
  METIS_TAC[bir_exec_infinite_steps_fun_COUNT_PCs_MONO_PC_COND] >>
Cases_on `c_st` >- (
  Q.UNABBREV_TAC `cc` >>
  Q.EXISTS_TAC `n1` >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def]
) >>
rename1 `SUC c_st'` >>

Cases_on `n1` >- (
  Q.UNABBREV_TAC `cc` >>
  Q.EXISTS_TAC `0` >>
  Q.PAT_X_ASSUM `!n. n < _ ==> _` (MP_TAC o Q.SPEC `0`) >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def,
    arithmeticTheory.NOT_LESS]
) >>
rename1 `SUC n1' <= _` >>

Cases_on `n1' < cc` >- (
  Cases_on `bir_state_COUNT_PC pc_cond' st'` >- (
    Q.EXISTS_TAC `cc` >>
    Q.UNABBREV_TAC `cc` >>
    FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
    ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_THM] >>
    REPEAT STRIP_TAC  >>
    `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st n <=
     bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st c_st'` by
       METIS_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_MONO] >>
    DECIDE_TAC
  ) >- (
    Q.EXISTS_TAC `SUC cc` >>
    `~(bir_state_COUNT_PC pc_cond st')` by METIS_TAC[bir_state_COUNT_PC_MONO] >>
    FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
    Q.UNABBREV_TAC `cc` >>
    ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_THM] >>
    REPEAT STRIP_TAC  >>
    `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st n <=
     bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st c_st'` by
       METIS_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_MONO] >>
    DECIDE_TAC
  )
) >- (
  Q.EXISTS_TAC `SUC n1'` >>
  FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
  Q.UNABBREV_TAC `cc` >>
  REPEAT STRIP_TAC >>
  `SUC n1' <=
   bir_exec_infinite_steps_fun_COUNT_PCs pc_cond' p st (SUC c_st')` by
       METIS_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_MONO,
                  arithmeticTheory.LESS_EQ_SUC_REFL,
                  arithmeticTheory.LESS_EQ_TRANS] >>
  DECIDE_TAC
));




(**************************************)
(* conversions for concrete instances *)
(**************************************)


val bir_exec_steps_GEN_TO_bir_exec_step_n = store_thm ("bir_exec_steps_GEN_TO_bir_exec_step_n",
  ``!p st st' mo c_st c_pc ol pc_cond.
    (bir_exec_steps_GEN pc_cond p st mo = BER_Ended ol c_st c_pc st') ==>
    (bir_exec_step_n p st c_st = (ol, c_st, st'))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_GEN_EQ_Ended, bir_exec_step_n_EQ_THM]);

val bir_exec_steps_TO_bir_exec_step_n = store_thm ("bir_exec_steps_TO_bir_exec_step_n",
  ``!p st st' ol c_st c_pc.
    (bir_exec_steps p st = BER_Ended ol c_st c_pc st') <=>
    ((bir_exec_step_n p st c_st = (ol, c_st, st')) /\ (c_pc = c_st) /\
      (bir_state_is_terminated st'))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_EQ_Ended,
  bir_exec_step_n_EQ_THM]);


val bir_exec_block_n_TO_bir_exec_step_n = store_thm ("bir_exec_block_n_TO_bir_exec_step_n",
  ``!p st st' ol c_st c_pc m.
    (bir_exec_block_n p st m = (ol, c_st, c_pc, st')) ==>
    (bir_exec_step_n p st c_st = (ol, c_st, st'))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_block_n_EQ_THM,
  bir_exec_step_n_EQ_THM]);


val bir_exec_to_labels_n_change_labels = store_thm ("bir_exec_to_labels_n_change_labels",
  ``!ls p st n ls' st' ol c_st c_l.
    (ls SUBSET ls') ==>
    (bir_exec_to_labels_n ls p st n = BER_Ended ol c_st c_l st') ==>
    (?n' c_l'. (n <= n') /\
               (bir_exec_to_labels_n ls' p st n' = BER_Ended ol c_st c_l' st'))``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`(F, \pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls)`,
                 `(F, \pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls')`,
                 `p`, `st`, `n`] bir_exec_steps_GEN_change_cond_Ended_SOME) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [SUBSET_DEF, bir_pc_cond_impl_def]);


val bir_exec_to_labels_n_TO_bir_exec_block_n = store_thm ("bir_exec_to_labels_n_TO_bir_exec_block_n",
  ``!ls p st n st' ol c_st c_l .
    (bir_exec_to_labels_n ls p st n = BER_Ended ol c_st c_l st') ==>
    (?m c_l'. (n <= m) /\ (bir_exec_block_n p st m = (ol, c_st, c_l', st')))``,

SIMP_TAC std_ss [bir_exec_block_n_TO_bir_exec_to_labels_n] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`ls`, `p`, `st`, `n`, `UNIV`] bir_exec_to_labels_n_change_labels) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [SUBSET_UNIV]);


val bir_exec_to_labels_n_TO_bir_exec_step_n = store_thm ("bir_exec_to_labels_n_TO_bir_exec_step_n",
  ``!ls p st n st' ol c_st c_l .
    (bir_exec_to_labels_n ls p st n = BER_Ended ol c_st c_l st') ==>
    (bir_exec_step_n p st c_st = (ol, c_st, st'))``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def,
  bir_exec_step_n_EQ_THM, bir_exec_steps_GEN_EQ_Ended])



val bir_exec_to_labels_n_TO_bir_exec_steps = store_thm ("bir_exec_to_labels_n_TO_bir_exec_steps",
  ``!ls p st n ll .
    (bir_exec_to_labels_n ls p st n = BER_Looping ll) ==>
    (bir_exec_steps p st = BER_Looping ll)``,

SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_steps_def] >>
METIS_TAC[bir_exec_steps_GEN_change_cond_Looping_NONE]);


val bir_exec_step_n_LIMIT_STEP_NO = store_thm ("bir_exec_step_n_LIMIT_STEP_NO",
  ``!p st n l st' c.
    (bir_exec_step_n p st n = (l, c, st')) ==>
    (bir_exec_step_n p st c = (l, c, st'))``,

SIMP_TAC std_ss [bir_exec_step_n_EQ_THM]);


(***********************************************)
(* alternative definition: bir_exec_step_n_acc *)
(***********************************************)

val bir_exec_step_n_acc_def = Define `
  bir_exec_step_n_acc (p:'a bir_program_t) (n:num) (aol:'a list, an:num, s:bir_state_t) =
            if (n = 0) \/ (bir_state_is_terminated s) then
              (REVERSE aol, an, s)
            else
              let
                (fe, s') = bir_exec_step p s
              in
                bir_exec_step_n_acc p (n-1) (OPT_CONS fe aol, an + 1, s')
`;

val bir_exec_step_n_acc_REWR_0 = store_thm("bir_exec_step_n_acc_REWR_0", ``
  !(p:'a bir_program_t) aol an s.
           bir_exec_step_n_acc p 0 (aol, an, s) = (REVERSE aol, an, s)
``,
  SIMP_TAC list_ss [Once bir_exec_step_n_acc_def]
);

val bir_exec_step_n_acc_REWR_TERMINATED = store_thm("bir_exec_step_n_acc_REWR_TERMINATED", ``
  !(p:'a bir_program_t) n aol an s.
           bir_state_is_terminated s ==>
           (bir_exec_step_n_acc p n (aol, an, s) = (REVERSE aol, an, s))
``,
  REPEAT STRIP_TAC >>
  ASM_SIMP_TAC list_ss [Once bir_exec_step_n_acc_def]
);

val bir_exec_step_n_acc_REWR_NOT_TERMINATED = store_thm("bir_exec_step_n_acc_REWR_NOT_TERMINATED", ``
  !(p:'a bir_program_t) n aol an s.
           ((~bir_state_is_terminated s) /\ (~(n = 0))) ==>
           (bir_exec_step_n_acc p n (aol, an, s) =
            (let
               (fe, s') = bir_exec_step p s
             in
               bir_exec_step_n_acc p (n-1) (OPT_CONS fe aol, an + 1, s')
            )
           )
``,
  REPEAT STRIP_TAC >>
  ASM_SIMP_TAC list_ss [Once bir_exec_step_n_acc_def]
);




val bir_exec_step_n_plus_acc_thm = store_thm("bir_exec_step_n_plus_acc_thm", ``
  !p s n aol an. (bir_exec_step_n_acc (p:'a bir_program_t) n (aol, an, s)) =
                 (\(ol, sn, s'). (APPEND (REVERSE aol) ol, sn + an, s')) (bir_exec_step_n p s n)
``,
  Induct_on `n` >- (
    SIMP_TAC list_ss [bir_exec_step_n_REWR_0, bir_exec_step_n_acc_REWR_0]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `bir_state_is_terminated s` >- (
    ASM_SIMP_TAC list_ss [bir_exec_step_n_REWR_TERMINATED, bir_exec_step_n_acc_REWR_TERMINATED]
  ) >>

  POP_ASSUM (fn thm => ASSUME_TAC thm >> ASSUME_TAC (MP (Q.SPECL [`p`, `s`, `n`] bir_exec_step_n_REWR_NOT_TERMINATED) thm)) >>
  POP_ASSUM (fn thm => REWRITE_TAC [thm]) >>

  POP_ASSUM (fn thm => ASSUME_TAC (MP (Q.SPECL [`p`, `SUC n`, `aol`, `an`, `s`] bir_exec_step_n_acc_REWR_NOT_TERMINATED) (CONJ thm (prove(``~(SUC n = 0)``, SIMP_TAC arith_ss []))))) >>
  POP_ASSUM (fn thm => REWRITE_TAC [thm]) >>

  SIMP_TAC arith_ss [] >>

  Cases_on `bir_exec_step p s` >>
  Q.RENAME1_TAC `bir_exec_step p s = (fe,s')` >>
  ASM_SIMP_TAC std_ss [LET_DEF] >>

  Cases_on `bir_exec_step_n p s' n` >>
  Q.RENAME1_TAC `bir_exec_step_n p s' n = (ol, x)` >>
  Cases_on `x` >>
  Q.RENAME1_TAC `bir_exec_step_n p s' n = (ol, sn, s'')` >>
  ASM_SIMP_TAC std_ss [LET_DEF] >>

  POP_ASSUM (fn thm => REWRITE_TAC [thm]) >>

  SIMP_TAC arith_ss [] >>

  SIMP_TAC list_ss [OPT_CONS_APPEND, OPT_CONS_REVERSE] >>
  Q.RENAME1_TAC `OPT_CONS fe []` >>
  SIMP_TAC list_ss [OPT_CONS_def] >>
  Cases_on `fe` >> (
    SIMP_TAC list_ss []
  ) >>

  SIMP_TAC std_ss [listTheory.APPEND, GSYM listTheory.APPEND_ASSOC]
);






val bir_exec_step_n_acc_eq_thm = store_thm("bir_exec_step_n_acc_eq_thm", ``
  !p s n. bir_exec_step_n_acc (p:'a bir_program_t) n ([], 0, s) =
          bir_exec_step_n     p s n
``,

  REWRITE_TAC [bir_exec_step_n_plus_acc_thm] >>
  SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  
  Q.RENAME1_TAC `bir_exec_step_n p s n` >>
  Cases_on `bir_exec_step_n p s n` >>
  Q.RENAME1_TAC `bir_exec_step_n p s n = (ol, x)` >>
  Cases_on `x` >>

  SIMP_TAC std_ss []
);






val _ = export_theory();
