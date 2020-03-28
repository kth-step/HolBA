open HolKernel Parse boolLib bossLib;
open listTheory
open bir_programTheory bir_program_valid_stateTheory HolBACoreSimps;
open bir_program_multistep_propsTheory bir_auxiliaryTheory
open bir_valuesTheory bir_immTheory bir_program_valid_stateTheory
open bir_program_terminationTheory
open sortingTheory pred_setTheory

val _ = new_theory "bir_subprogram";


(* ------------------------------------------------------------------------- *)
(* We often might want to reason about parts of a program in isolation.      *)
(* Let's say we reason about some function "fun_A" that is implemented by    *)
(* multiple code blocks. After we finished this reasoning, we want to        *)
(* use this function in a function "fun_B" using our previous results        *)
(* Some basic reasoning like this is enabled by this theory                  *)
(* ------------------------------------------------------------------------- *)


(*****************************)
(* Definition of subprograms *)
(*****************************)

(* a program is a subprogram of another one, if all blocks of the
   subprogram are available in the larger one. They might be in a different
   order, though. No extra duplication is allowed. *)

val bir_is_subprogram_def = Define `bir_is_subprogram (BirProgram p_sub) (BirProgram p) <=>
  (?l'. PERM (p_sub ++ l') p)`;


(* The subprogram relation is an order *)
val bir_is_subprogram_REFL = store_thm ("bir_is_subprogram_REFL",
  ``!p. bir_is_subprogram p p``,

Cases >>
SIMP_TAC std_ss [bir_is_subprogram_def] >>
Q.EXISTS_TAC `[]` >>
SIMP_TAC list_ss [PERM_REFL]);


val bir_is_subprogram_TRANS = store_thm ("bir_is_subprogram_TRANS",
  ``!p1 p2 p3. bir_is_subprogram p1 p2 ==> (bir_is_subprogram p2 p3) ==> bir_is_subprogram p1 p3``,

REPEAT Cases >>
SIMP_TAC std_ss [bir_is_subprogram_def] >>
`!(l1:'a bir_block_t list) l2 l3 l4 l5.
   PERM (l1 ++ l2) l3 ==>
   PERM (l3 ++ l4) l5 ==>
   PERM (l1 ++ (l2 ++ l4)) l5` suffices_by METIS_TAC[] >>
SIMP_TAC (std_ss++permLib.PERM_ss) []);


(**********************************)
(* Definition of program equality *)
(**********************************)

val bir_program_eq_def = Define `bir_program_eq (BirProgram p1) (BirProgram p2) <=>
  PERM p1 p2`;

(* This is - as can be seen easily - a congruence relation *)
val bir_program_eq_REFL = store_thm ("bir_program_eq_REFL",
  ``!p. bir_program_eq p p``,
Cases >> SIMP_TAC std_ss [bir_program_eq_def, PERM_REFL]);

val bir_program_eq_SYM = store_thm ("bir_program_eq_SYM",
  ``!p1 p2. (bir_program_eq p1 p2) <=> (bir_program_eq p2 p1)``,
REPEAT Cases >> SIMP_TAC std_ss [bir_program_eq_def, PERM_SYM]);

val bir_program_eq_TRANS = store_thm ("bir_program_eq_TRANS",
  ``!p1 p2 p3. (bir_program_eq p1 p2) ==> (bir_program_eq p2 p3) ==> bir_program_eq p1 p3``,
REPEAT Cases >> SIMP_TAC std_ss [bir_program_eq_def] >> METIS_TAC[PERM_TRANS]);


(* more interestingly, the equivalence is related to the subprogram order in the
   expected way. *)

val bir_is_subprogram_ANTISYM = store_thm ("bir_is_subprogram_ANTISYM",
``!p1 p2. (bir_program_eq p1 p2) <=> ((bir_is_subprogram p1 p2) /\ (bir_is_subprogram p2 p1))``,

REPEAT Cases >>
rename1 `bir_program_eq (BirProgram p1) (BirProgram p2)` >>
SIMP_TAC std_ss [bir_is_subprogram_def, bir_program_eq_def] >>
EQ_TAC >> REPEAT STRIP_TAC >| [
  Q.EXISTS_TAC `[]` >> ASM_SIMP_TAC list_ss [],

  Q.EXISTS_TAC `[]` >> ASM_SIMP_TAC list_ss [PERM_SYM],

  rename1 `PERM (p1 ++ p1') p2` >>
  rename1 `PERM (p2 ++ p2') p1` >>
  `LENGTH p1 + LENGTH p1' = LENGTH p2` by METIS_TAC[PERM_LENGTH, listTheory.LENGTH_APPEND] >>
  `LENGTH p2 + LENGTH p2' = LENGTH p1` by METIS_TAC[PERM_LENGTH, listTheory.LENGTH_APPEND] >>
  `LENGTH p1' = 0` by DECIDE_TAC >>
  FULL_SIMP_TAC list_ss []
]);


(* The program equality is therefore compatible with subprograms *)

val bir_subprogram_eq_cong = store_thm ("bir_subprogram_eq_cong",
``!p_sub p_sub' p p'.
   bir_program_eq p p' ==>
   bir_program_eq p_sub p_sub' ==>
   (bir_is_subprogram p_sub p <=> bir_is_subprogram p_sub' p')``,

SIMP_TAC std_ss [bir_is_subprogram_ANTISYM] >>
METIS_TAC[bir_is_subprogram_TRANS]);


(*************************************)
(* Definition of program combination *)
(*************************************)

(* The most common way of creating programs is by combining programs *)

val bir_program_combine_def = Define `
  bir_program_combine (BirProgram p1) (BirProgram p2) =
  BirProgram (p1 ++ p2)`

val bir_program_combine_SUBPROGRAMS = store_thm ("bir_program_combine_SUBPROGRAMS",
  ``(!p1 p2. bir_is_subprogram p1 (bir_program_combine p1 p2)) /\
    (!p1 p2. bir_is_subprogram p2 (bir_program_combine p1 p2))``,

CONJ_TAC >>
REPEAT Cases >> (
  SIMP_TAC std_ss [bir_is_subprogram_def, bir_program_combine_def] >>
  METIS_TAC[PERM_REFL, PERM_APPEND]
));


val bir_program_combine_NEUTRAL = store_thm ("bir_program_combine_NEUTRAL",
  ``(!p. bir_program_combine p (BirProgram []) = p) /\
    (!p. bir_program_combine (BirProgram []) p = p)``,

CONJ_TAC >> (
  Cases >>
  SIMP_TAC list_ss [bir_program_combine_def]
));


val bir_program_combine_COMM = store_thm ("bir_program_combine_COMM",
  ``!p1 p2. bir_program_eq (bir_program_combine p1 p2) (bir_program_combine p2 p1)``,

REPEAT Cases >>
SIMP_TAC list_ss [bir_program_combine_def, bir_program_eq_def] >>
METIS_TAC[PERM_APPEND]);


val bir_program_combine_ASSOC = store_thm ("bir_program_combine_ASSOC",
  ``!p1 p2 p3. (bir_program_combine p1 (bir_program_combine p2 p3)) =
               (bir_program_combine (bir_program_combine p1 p2) p3)``,

REPEAT Cases >>
SIMP_TAC list_ss [bir_program_combine_def]);



(**********)
(* blocks *)
(**********)

val bir_is_subprogram_BLOCKS_SUBLIST = store_thm ("bir_is_subprogram_BLOCKS_SUBLIST",
  ``!p_sub p. bir_is_subprogram (BirProgram p_sub) (BirProgram p) ==>
              (!bl. MEM bl p_sub ==> MEM bl p)``,
SIMP_TAC std_ss [bir_is_subprogram_def] >>
METIS_TAC[PERM_MEM_EQ, listTheory.MEM_APPEND]);

val bir_program_eq_BLOCKS_EQ = store_thm ("bir_program_eq_BLOCKS_EQ",
  ``!p1 p2. bir_program_eq (BirProgram p1) (BirProgram p2) ==>
              (!bl. MEM bl p1 <=> MEM bl p2)``,
SIMP_TAC std_ss [bir_program_eq_def] >>
METIS_TAC[PERM_MEM_EQ]);


(**********************)
(* labels of programs *)
(**********************)

val bir_labels_of_program_SUBPROGRAM = store_thm ("bir_labels_of_program_SUBPROGRAM",
``!p1 p2. bir_is_subprogram p1 p2 ==>
          (!l. MEM l (bir_labels_of_program p1) ==> MEM l (bir_labels_of_program p2))``,
REPEAT Cases >>
SIMP_TAC list_ss [bir_labels_of_program_def, bir_is_subprogram_def, MEM_MAP] >>
REPEAT STRIP_TAC >>
METIS_TAC[PERM_MEM_EQ, MEM_APPEND]);


val bir_labels_of_program_PROGRAM_EQ = store_thm ("bir_labels_of_program_PROGRAM_EQ",
``!p1 p2. bir_program_eq p1 p2 ==>
          (!l. MEM l (bir_labels_of_program p1) <=> MEM l (bir_labels_of_program p2))``,

SIMP_TAC std_ss [bir_is_subprogram_ANTISYM] >>
METIS_TAC[bir_labels_of_program_SUBPROGRAM]);


val bir_labels_of_program_PROGRAM_COMBINE = store_thm ("bir_labels_of_program_PROGRAM_COMBINE",
``!p1 p2. bir_labels_of_program (bir_program_combine p1 p2) =
          (bir_labels_of_program p1) ++ (bir_labels_of_program p2)``,

REPEAT Cases >>
SIMP_TAC list_ss [bir_labels_of_program_def, bir_program_combine_def]);


(***********************)
(* bir_is_valid_labels *)
(***********************)

val bir_is_valid_labels_SUBPROGRAM = store_thm ("bir_is_valid_labels_SUBPROGRAM",
``!p1 p2. bir_is_subprogram p1 p2 ==>
          bir_is_valid_labels p2 ==>
          bir_is_valid_labels p1``,

REPEAT Cases >>
SIMP_TAC std_ss [bir_is_valid_labels_def, bir_is_subprogram_def, bir_labels_of_program_def] >>
REPEAT STRIP_TAC >>
rename1 `PERM (l1 ++ l2) l3` >>
`ALL_DISTINCT (MAP (\bl. bl.bb_label) (l1 ++ l2))` by METIS_TAC[ALL_DISTINCT_PERM, PERM_MAP] >>
FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND]);


val bir_is_valid_labels_PROGRAM_EQ = store_thm ("bir_is_valid_labels_PROGRAM_EQ",
``!p1 p2. bir_program_eq p1 p2 ==>
          (bir_is_valid_labels p1 <=> bir_is_valid_labels p2)``,

METIS_TAC[bir_is_subprogram_ANTISYM, bir_is_valid_labels_SUBPROGRAM]);


val bir_is_valid_labels_PROGRAM_COMBINE = store_thm ("bir_is_valid_labels_PROGRAM_COMBINE",
``!p1 p2. bir_is_valid_labels (bir_program_combine p1 p2) <=>
          (bir_is_valid_labels p1 /\ bir_is_valid_labels p2 /\
           (!l. ~(MEM l (bir_labels_of_program p1)) \/ ~(MEM l (bir_labels_of_program p2))))``,

REPEAT Cases >>
SIMP_TAC list_ss [bir_labels_of_program_def, bir_is_valid_labels_def,
  bir_program_combine_def, ALL_DISTINCT_APPEND] >>
METIS_TAC[]);



(************************)
(* bir_is_empty_program *)
(************************)

val bir_program_is_empty_SUBPROGRAM = store_thm ("bir_program_is_empty_SUBPROGRAM",
``!p1 p2. bir_is_subprogram p1 p2 ==>
          bir_program_is_empty p2 ==>
          bir_program_is_empty p1``,

REPEAT Cases >>
SIMP_TAC std_ss [bir_is_subprogram_def, bir_program_is_empty_def, NULL_EQ] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [PERM_NIL]);


val bir_program_is_empty_PROGRAM_EQ = store_thm ("bir_program_is_empty_PROGRAM_EQ",
``!p1 p2. bir_program_eq p1 p2 ==>
          (bir_program_is_empty p1 <=> bir_program_is_empty p2)``,

METIS_TAC[bir_is_subprogram_ANTISYM, bir_program_is_empty_SUBPROGRAM]);


val bir_program_is_empty_PROGRAM_COMBINE = store_thm ("bir_program_is_empty_PROGRAM_COMBINE",
``!p1 p2. bir_program_is_empty (bir_program_combine p1 p2) <=>
          (bir_program_is_empty p1 /\ bir_program_is_empty p2)``,

REPEAT Cases >>
SIMP_TAC list_ss [bir_program_is_empty_def, NULL_EQ, bir_program_combine_def])



(*****************************)
(* bir_get_current_statement *)
(*****************************)

val bir_get_program_block_info_by_label_SUBPROGRAM = store_thm ("bir_get_program_block_info_by_label_SUBPROGRAM",
``!p1 p2 l n1 bl.
          bir_is_subprogram p1 p2 ==>
          bir_is_valid_labels p2 ==>
          (bir_get_program_block_info_by_label p1 l = SOME (n1, bl)) ==>
          ?n2. (bir_get_program_block_info_by_label p2 l = SOME (n2, bl))``,

Cases >> Cases >>
rename1 `bir_is_subprogram (BirProgram p1) (BirProgram p2)` >>
REPEAT STRIP_TAC >>
`bir_is_valid_labels (BirProgram p1)` by METIS_TAC[bir_is_valid_labels_SUBPROGRAM] >>
FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_valid_THM] >>
METIS_TAC[MEM_EL, bir_is_subprogram_BLOCKS_SUBLIST]);


val bir_is_valid_pc_SUBPROGRAM = store_thm ("bir_is_valid_pc_SUBPROGRAM",
``!p1 p2 pc.
          bir_is_subprogram p1 p2 ==>
          bir_is_valid_labels p2 ==>
          bir_is_valid_pc p1 pc ==>
          bir_is_valid_pc p2 pc``,

REPEAT STRIP_TAC >>
`bir_is_valid_labels p1` by METIS_TAC[bir_is_valid_labels_SUBPROGRAM] >>
FULL_SIMP_TAC std_ss [bir_is_valid_pc_def] >>
METIS_TAC[bir_get_program_block_info_by_label_SUBPROGRAM]);


val bir_is_valid_pc_PROGRAM_EQ = store_thm ("bir_is_valid_pc_PROGRAM_EQ",
``!p1 p2 pc.
          bir_program_eq p1 p2 ==>
          bir_is_valid_labels p2 ==>
          (bir_is_valid_pc p1 pc <=> bir_is_valid_pc p2 pc)``,

METIS_TAC[bir_is_subprogram_ANTISYM, bir_is_valid_labels_PROGRAM_EQ,
  bir_is_valid_pc_SUBPROGRAM]);


val bir_get_current_statement_SUBPROGRAM = store_thm ("bir_get_current_statement_SUBPROGRAM",
``!p1 p2 pc stmt.
          bir_is_subprogram p1 p2 ==>
          bir_is_valid_labels p2 ==>
          (bir_get_current_statement p1 pc = SOME stmt) ==>
          (bir_get_current_statement p2 pc = SOME stmt)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_get_current_statement_def] >>
Cases_on `bir_get_program_block_info_by_label p1 pc.bpc_label` >- (
  FULL_SIMP_TAC std_ss []
) >>
rename1 `bir_get_program_block_info_by_label p1 pc.bpc_label = SOME xx` >>
Cases_on `xx` >>
rename1 `bir_get_program_block_info_by_label p1 pc.bpc_label = SOME (i, bl)` >>

`?i'. bir_get_program_block_info_by_label p2 pc.bpc_label = SOME (i', bl)` by
  METIS_TAC[bir_get_program_block_info_by_label_SUBPROGRAM] >>
FULL_SIMP_TAC std_ss []);


val bir_get_current_statement_PROGRAM_EQ = store_thm ("bir_get_current_statement_PROGRAM_EQ",
``!p1 p2 pc.
          bir_program_eq p1 p2 ==>
          bir_is_valid_labels p2 ==>
          (bir_get_current_statement p1 pc = bir_get_current_statement p2 pc)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_subprogram_ANTISYM] >>
`bir_is_valid_labels p1` by METIS_TAC[bir_is_valid_labels_SUBPROGRAM] >>
Tactical.REVERSE (Cases_on `bir_get_current_statement p1 pc`) >- (
  METIS_TAC [bir_get_current_statement_SUBPROGRAM]
) >>
Cases_on `bir_get_current_statement p2 pc` >- REWRITE_TAC[] >>
METIS_TAC [bir_get_current_statement_SUBPROGRAM, optionTheory.option_CLAUSES]);


(*************)
(* Semantics *)
(*************)

(* Now the main part. We want to say that if a subprogram executes without leaving the
   subprogram, i.e. if

   - we start with a valid pc
   - we don't jump out of the program, i.e. we don't terminate with status
     "BST_JumpOutside l"

   then the execution of the larger program does exactly the same.

   If we jump outside, i.e. have status "BST_JumpOutside l", there are 2 options:

   a) The larger program does not know label "l" either. It behaves the same.
   b) The larger program does know it, and executed the jump successfully


   Basic statements do not look at the program. This is even clear by syntax. So,
   we just need to reason about end staments and the lift the results to executing a single step
   and finally multiple steps.
*)

val bir_jumped_outside_termination_cond_def = Define `
  bir_jumped_outside_termination_cond (p1 : 'a bir_program_t) (p2 : 'a bir_program_t) st1 st2 <=>
  ?l. (st1.bst_status = BST_JumpOutside l) /\
      (MEM l (bir_labels_of_program p2)) /\
      ~(MEM l (bir_labels_of_program p1)) /\
      (st2 = (st1 with <| bst_status := BST_Running;
                          bst_pc := (bir_block_pc l) |>))`;

val bir_jumped_outside_termination_cond_NOT_PROGRAM_EQ = store_thm (
  "bir_jumped_outside_termination_cond_NOT_PROGRAM_EQ",
``!p1 p2 st1 st2.
    bir_program_eq p1 p2 ==>
    ~(bir_jumped_outside_termination_cond p1 p2 st1 st2)``,

SIMP_TAC std_ss [bir_jumped_outside_termination_cond_def] >>
METIS_TAC[bir_labels_of_program_PROGRAM_EQ]);


val bir_jumped_outside_termination_cond_TERMINATED_LEFT = store_thm (
  "bir_jumped_outside_termination_cond_TERMINATED_LEFT",
``!p1 p2 st1 st2.
    ~(bir_state_is_terminated st1) ==>
    ~(bir_jumped_outside_termination_cond p1 p2 st1 st2)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [
  bir_jumped_outside_termination_cond_def, bir_state_is_terminated_def]);


val bir_jumped_outside_termination_cond_TERMINATED_RIGHT = store_thm (
  "bir_jumped_outside_termination_cond_TERMINATED_RIGHT",
``!p1 p2 st1 st2.
    bir_state_is_terminated st2 ==>
    ~(bir_jumped_outside_termination_cond p1 p2 st1 st2)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [
  bir_jumped_outside_termination_cond_def, bir_state_is_terminated_def,
  bir_state_t_component_equality]);


val bir_jumped_outside_termination_cond_STATE_NEQ = store_thm (
  "bir_jumped_outside_termination_cond_STATE_NEQ",
``!p1 p2 st.
    ~(bir_jumped_outside_termination_cond p1 p2 st st)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [
  bir_jumped_outside_termination_cond_def,
  bir_state_t_component_equality] >>
REPEAT GEN_TAC >>
Cases_on `st.bst_status` >> SIMP_TAC (std_ss++bir_TYPES_ss) []);


(* Now the real lemma *)
val bir_exec_stmtE_SUBPROGRAM = store_thm ("bir_exec_stmtE_SUBPROGRAM",
``!p1 p2.
  bir_is_subprogram p1 p2 ==> !stmt st st1 st2.
  ~(bir_state_is_terminated st) ==>
  (bir_exec_stmtE p1 stmt st = st1) ==>
  (bir_exec_stmtE p2 stmt st = st2) ==>
  (bir_jumped_outside_termination_cond p1 p2 st1 st2) \/
  ((!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) /\
   (st1 = st2))``,

REPEAT GEN_TAC >> STRIP_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`] bir_labels_of_program_SUBPROGRAM)  >>
ASM_REWRITE_TAC [] >> STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, bir_jumped_outside_termination_cond_def,
    bir_exec_stmt_jmp_def, LET_THM, bir_exec_stmt_jmp_to_label_def, bir_state_is_terminated_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_t_component_equality, bir_state_set_typeerror_def] >>
  METIS_TAC[]
));


(* Lifting to executing a step *)
val bir_exec_step_SUBPROGRAM = store_thm ("bir_exec_step_SUBPROGRAM",
``!p1 p2 st st1 st2 fe1 fe2.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  ~(bir_state_is_terminated st) ==>
  (bir_exec_step p1 st = (fe1, st1)) ==>
  (bir_exec_step p2 st = (fe2, st2)) ==>
  ((fe1 = fe2) /\
  ((bir_jumped_outside_termination_cond p1 p2 st1 st2) \/
  ((!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) /\
   (st1 = st2))))``,


REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
`?stmt. bir_get_current_statement p1 st.bst_pc = SOME stmt` by
  METIS_TAC[bir_get_current_statement_IS_SOME, optionTheory.IS_SOME_EXISTS] >>
`bir_get_current_statement p2 st.bst_pc = SOME stmt` by
  METIS_TAC[bir_get_current_statement_SUBPROGRAM] >>
FULL_SIMP_TAC std_ss [bir_exec_step_def] >>
REV_FULL_SIMP_TAC std_ss [] >>

Tactical.REVERSE (Cases_on `stmt`) >- (
  FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  METIS_TAC[bir_exec_stmtE_SUBPROGRAM]
) >>

FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >>
`!l. st1.bst_status <> BST_JumpOutside l` suffices_by METIS_TAC[] >>
REPEAT STRIP_TAC >>
`?oo st'. bir_exec_stmtB b st = (oo, st')` by METIS_TAC[pairTheory.PAIR] >>
`st'.bst_status = BST_JumpOutside l` by (
  Cases_on `bir_state_is_terminated st'` >> (
    FULL_SIMP_TAC std_ss [LET_THM] >>
    REPEAT BasicProvers.VAR_EQ_TAC >>
    FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [LET_THM]
  )
) >>
POP_ASSUM MP_TAC >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def, LET_THM] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
rename1 `bir_exec_stmtB stmtB st` >>
MP_TAC (Q.SPECL [`st`, `stmtB`] bir_exec_stmtB_status_not_jumped) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_stmtB_state_def]);



val bir_exec_step_PROGRAM_EQ = store_thm ("bir_exec_step_PROGRAM_EQ",
``!p1 p2 st.
  bir_program_eq p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_step p1 st = bir_exec_step p2 st)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`, `st`] bir_exec_step_SUBPROGRAM) >>
MP_TAC (Q.SPECL [`p2`, `p1`, `st`] bir_exec_step_SUBPROGRAM) >>

Cases_on `bir_state_is_terminated st` >- (
  ASM_SIMP_TAC std_ss [bir_exec_step_def]
) >>
Cases_on `bir_exec_step p1 st` >>
Cases_on `bir_exec_step p2 st` >>
rename1 `(fe1, st1) = (fe2, st2)` >>
ASM_SIMP_TAC std_ss [bir_jumped_outside_termination_cond_NOT_PROGRAM_EQ,
  bir_program_eq_SYM] >>
`bir_is_valid_pc p2 st.bst_pc = bir_is_valid_pc p1 st.bst_pc`
   by METIS_TAC[bir_is_valid_pc_PROGRAM_EQ] >>

Tactical.REVERSE (Cases_on `bir_is_valid_pc p1 st.bst_pc`) >- (
  FULL_SIMP_TAC std_ss [bir_exec_step_invalid_pc_THM]
) >>
FULL_SIMP_TAC std_ss [bir_is_subprogram_ANTISYM]);


val bir_exec_step_state_SUBPROGRAM = store_thm ("bir_exec_step_state_SUBPROGRAM",
``!p1 p2 st st1 st2.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  ~(bir_state_is_terminated st) ==>
  (bir_exec_step_state p1 st = st1) ==>
  (bir_exec_step_state p2 st = st2) ==>
  ((bir_jumped_outside_termination_cond p1 p2 st1 st2) \/
  ((!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) /\
   (st1 = st2)))``,

METIS_TAC[bir_exec_step_state_def, pairTheory.SND, pairTheory.PAIR,
  bir_exec_step_SUBPROGRAM]);


(**************************)
(* Lifting it to step_GEN *)
(**************************)


val bir_state_COUNT_PC_ENV_bir_jumped_outside_termination_cond = store_thm (
  "bir_state_COUNT_PC_ENV_bir_jumped_outside_termination_cond",
``!pc_env_cond p1 p2 st1 st2.
   bir_jumped_outside_termination_cond p1 p2 st1 st2 ==>
   (bir_state_COUNT_PC_ENV pc_env_cond st1 = bir_state_COUNT_PC_ENV pc_env_cond st2)``,

Cases >>
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_jumped_outside_termination_cond_def, PULL_EXISTS,
  bir_state_COUNT_PC_ENV_def]);



val bir_exec_steps_GEN_Ended_SUBPROGRAM = store_thm ("bir_exec_steps_GEN_Ended_SUBPROGRAM",
``!p1 p2 pc_env_cond st mo st1 l c_st c_pc.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  (!l. (st.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) ==>
  (bir_exec_steps_GEN pc_env_cond p1 st mo = BER_Ended l c_st c_pc st1) ==>
  (* We must be able to stop *)
  (bir_state_COUNT_PC_ENV pc_env_cond st1) ==>

  ?st2.
  (bir_exec_steps_GEN pc_env_cond p2 st (SOME c_pc) = BER_Ended l c_st c_pc st2) /\
  ((bir_jumped_outside_termination_cond p1 p2 st1 st2) \/
  ((!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) /\
   (st1 = st2)))``,


NTAC 3 GEN_TAC >>
Induct_on `c_st` >- (
  SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_0]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_SUC] >>

`?fe1 st1'. bir_exec_step p1 st = (fe1, st1')` by METIS_TAC[pairTheory.PAIR] >>
`?fe2 st2'. bir_exec_step p2 st = (fe2, st2')` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC arith_ss [LET_THM] >>
MP_TAC (Q.SPECL [`p1`, `p2`, `st`] bir_exec_step_SUBPROGRAM) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >- (
  `?l. (st1'.bst_status = BST_JumpOutside l) /\
        MEM l (bir_labels_of_program p2)` by METIS_TAC[bir_jumped_outside_termination_cond_def] >>
  `bir_state_COUNT_PC_ENV pc_env_cond st1' = bir_state_COUNT_PC_ENV pc_env_cond st2'` by
     METIS_TAC[bir_state_COUNT_PC_ENV_bir_jumped_outside_termination_cond] >>
  `bir_state_is_terminated st1'` by ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>

  FULL_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_TERMINATED] >>
  REPEAT (BasicProvers.VAR_EQ_TAC) >>
  FULL_SIMP_TAC (arith_ss++bir_TYPES_ss) [OPT_NUM_PRE_def,
    bir_exec_steps_GEN_EQ_Ended_0] >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_jumped_outside_termination_cond_def,
    bir_state_COUNT_PC_ENV_def]
) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
REPEAT BasicProvers.VAR_EQ_TAC >>

`bir_is_valid_pc p1 st1'.bst_pc` by (
   MP_TAC (Q.SPECL [`p1`, `st`] bir_exec_step_valid_pc) >>
   ASM_SIMP_TAC std_ss [bir_exec_step_state_def]
) >>

Q.PAT_X_ASSUM `!st'' mo'. _` (MP_TAC o Q.SPECL [`st1'`, `if bir_state_COUNT_PC_ENV pc_env_cond st1' then OPT_NUM_PRE mo else mo`]) >>

ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [OPT_NUM_PRE_def, PULL_EXISTS] >>
`~(bir_state_COUNT_PC_ENV pc_env_cond st1') ==> c_pc' <> 0` suffices_by METIS_TAC[numTheory.NOT_SUC] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended] >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>
Cases_on `c_st` >> (
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>
ASM_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_COUNT_PC_ENVs_END_DEF,
   bir_exec_infinite_steps_fun_REWRS, LET_THM]);



val bir_exec_steps_GEN_Ended_SUBPROGRAM_EQ = store_thm ("bir_exec_steps_GEN_Ended_SUBPROGRAM_EQ",
``!p1 p2 pc_env_cond st mo st1 l c_st c_pc.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  (!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) ==>
  (bir_exec_steps_GEN pc_env_cond p1 st mo = BER_Ended l c_st c_pc st1) ==>
  (bir_exec_steps_GEN pc_env_cond p2 st mo = BER_Ended l c_st c_pc st1)``,

NTAC 3 GEN_TAC >>
Induct_on `c_st` >- (
  SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_0]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_SUC] >>

`?fe1 st1''. bir_exec_step p1 st = (fe1, st1'')` by METIS_TAC[pairTheory.PAIR] >>
`?fe2 st2''. bir_exec_step p2 st = (fe2, st2'')` by METIS_TAC[pairTheory.PAIR] >>

`(fe1 = fe2) /\ (st1'' = st2'')` by (
   MP_TAC (Q.SPECL [`p1`, `p2`, `st`] bir_exec_step_SUBPROGRAM) >>
   ASM_SIMP_TAC std_ss [] >>
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC std_ss [bir_jumped_outside_termination_cond_def, LET_THM] >>
   `bir_state_is_terminated st1''` by ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>
   FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_TERMINATED] >>
   REPEAT (BasicProvers.VAR_EQ_TAC) >>
   METIS_TAC[]
) >>

`bir_is_valid_pc p1 st2''.bst_pc` by (
   MP_TAC (Q.SPECL [`p1`, `st`] bir_exec_step_valid_pc) >>
   ASM_SIMP_TAC std_ss [bir_exec_step_state_def]
) >>

FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_SUC,LET_THM] >>
Q.ABBREV_TAC `mo' = (if bir_state_COUNT_PC_ENV pc_env_cond st2'' then OPT_NUM_PRE mo else mo)` >>

Q.PAT_X_ASSUM `!st'' mo'. _` (MP_TAC o Q.SPECL [`st2''`, `mo'`]) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []);


val bir_state_is_terminated_step_not_valid_pc = store_thm ("bir_state_is_terminated_step_not_valid_pc",
``!p st. ~(bir_is_valid_pc p st.bst_pc) ==> bir_state_is_terminated (bir_exec_step_state p st)``,

REPEAT STRIP_TAC >>
`~(IS_SOME (bir_get_current_statement p st.bst_pc))` by
  METIS_TAC[bir_get_current_statement_IS_SOME] >>
FULL_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_step_def] >>
Cases_on `bir_state_is_terminated st` >> (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_failed_def, bir_state_is_terminated_def]
));


val bir_state_is_failed_step_not_valid_pc =
  store_thm ("bir_state_is_failed_step_not_valid_pc",
``!p st.
  ~(bir_state_is_terminated st) ==>
  ~(bir_is_valid_pc p st.bst_pc) ==>
  ((bir_exec_step_state p st).bst_status = BST_Failed)``,

REPEAT STRIP_TAC >>
`~(IS_SOME (bir_get_current_statement p st.bst_pc))` by
  (METIS_TAC [bir_get_current_statement_IS_SOME]) >>
  FULL_SIMP_TAC std_ss [bir_exec_step_state_def,
                        bir_exec_step_def] >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss)
  [bir_state_set_failed_def]
);


val bir_exec_infinite_steps_fun_SUBPROGRAM = store_thm ("bir_exec_infinite_steps_fun_SUBPROGRAM",
``!p1 p2.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (!st m.
    ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p1 st m)) ==>
    (bir_exec_infinite_steps_fun p1 st m = bir_exec_infinite_steps_fun p2 st m))``,

REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
Induct_on `m` >- (
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>
SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
REPEAT STRIP_TAC >>
Q.ABBREV_TAC `st' = bir_exec_step_state p1 st` >>
`~(bir_state_is_terminated st')` by (
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_TERMINATED_0]
) >>
`~(bir_state_is_terminated st)` by (
  Q.UNABBREV_TAC `st'` >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_step_def]
) >>
`bir_is_valid_pc p1 st.bst_pc` by METIS_TAC[bir_state_is_terminated_step_not_valid_pc] >>
`bir_exec_step_state p2 st = st'` by (
  MP_TAC (Q.SPECL [`p1`, `p2`, `st`] bir_exec_step_state_SUBPROGRAM) >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_jumped_outside_termination_cond_def,
    bir_state_is_terminated_def]
) >>
`bir_is_valid_pc p1 st'.bst_pc` by METIS_TAC[bir_exec_step_valid_pc] >>
METIS_TAC[]);



val bir_exec_steps_GEN_Looping_SUBPROGRAM = store_thm ("bir_exec_steps_GEN_Looping_SUBPROGRAM",
``!p1 p2 pc_env_cond st mo ll.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_steps_GEN pc_env_cond p1 st mo = BER_Looping ll) ==>
  (bir_exec_steps_GEN pc_env_cond p2 st mo = BER_Looping ll)``,

SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Looping,
  bir_exec_steps_observe_llist_def,
  bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
`bir_exec_infinite_steps_fun p2 st = bir_exec_infinite_steps_fun p1 st` by
  METIS_TAC[bir_exec_infinite_steps_fun_SUBPROGRAM, FUN_EQ_THM] >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PC_ENVs_ALT_DEF,
  bir_exec_infinite_steps_fun_PC_ENV_COND_SET_def] >>
`!i. FST (bir_exec_step p1 (bir_exec_infinite_steps_fun p1 st i)) =
     FST (bir_exec_step p2 (bir_exec_infinite_steps_fun p1 st i))` suffices_by
   FULL_SIMP_TAC std_ss [] >>

GEN_TAC >>
Q.ABBREV_TAC `st'' = bir_exec_infinite_steps_fun p1 st i` >>
`bir_is_valid_pc p1 st''.bst_pc` by (
  Q.PAT_ASSUM `!n. _` (MP_TAC o Q.SPEC `SUC i`) >>
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2] >>
  METIS_TAC[bir_state_is_terminated_step_not_valid_pc]
) >>
METIS_TAC[bir_exec_step_SUBPROGRAM, pairTheory.FST, pairTheory.PAIR]);



val bir_exec_steps_GEN_Ended_PROGRAM_EQ = prove (
``!p1 p2 pc_env_cond st mo st' l c_st c_pc.
  bir_program_eq p1 p2 ==>
  bir_is_valid_labels p2 ==>

  (bir_exec_steps_GEN pc_env_cond p1 st mo = BER_Ended l c_st c_pc st') ==>
  (bir_exec_steps_GEN pc_env_cond p2 st mo = BER_Ended l c_st c_pc st')``,

NTAC 3 GEN_TAC >>
Induct_on `c_st` >- (
  SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_0]
) >>
REPEAT STRIP_TAC >>

`?fe st''. bir_exec_step p1 st = (fe, st'')` by METIS_TAC[pairTheory.PAIR] >>
`bir_exec_step p2 st = (fe, st'')` by METIS_TAC[bir_exec_step_PROGRAM_EQ] >>

FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_EQ_Ended_SUC,LET_THM] >>
Q.ABBREV_TAC `mo' = (if bir_state_COUNT_PC_ENV pc_env_cond st'' then OPT_NUM_PRE mo else mo)` >>

Q.PAT_X_ASSUM `!st'' mo'. _` (MP_TAC o Q.SPECL [`st''`, `mo'`]) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []);



val bir_exec_steps_GEN_PROGRAM_EQ = store_thm ("bir_exec_steps_GEN_PROGRAM_EQ",
``!p1 p2 pc_env_cond.
  bir_program_eq p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_steps_GEN pc_env_cond p1 = bir_exec_steps_GEN pc_env_cond p2)``,

SIMP_TAC std_ss [FUN_EQ_THM] >>
REPEAT STRIP_TAC >>
rename1 `bir_exec_steps_GEN pc_env_cond p1 st mo` >>
Cases_on `bir_exec_steps_GEN pc_env_cond p1 st mo` >- (
  METIS_TAC[bir_exec_steps_GEN_Ended_PROGRAM_EQ]
) >- (
  METIS_TAC[bir_exec_steps_GEN_Looping_SUBPROGRAM, bir_is_subprogram_ANTISYM]
));



(************************)
(* Lifting it to step_n *)
(************************)

val bir_exec_step_n_SUBPROGRAM = store_thm ("bir_exec_step_n_SUBPROGRAM",
``!p1 p2 st c st1 st2 l1 l2 n1 n2.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  (!l. (st.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) ==>
  (bir_exec_step_n p1 st c  = (l1, n1, st1)) ==>
  (bir_exec_step_n p2 st n1 = (l2, n2, st2)) ==>
  ((n2 = n1) /\ (l2 = l1) /\
  ((bir_jumped_outside_termination_cond p1 p2 st1 st2) \/
  ((!l. (st1.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) /\
   (st1 = st2))))``,

REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`, `(T, \_ _. T)`, `st`, `SOME c`] bir_exec_steps_GEN_Ended_SUBPROGRAM) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_n_TO_steps_GEN,
  bir_state_COUNT_PC_ENV_ALL_STEPS]);


val bir_exec_step_n_PROGRAM_EQ = store_thm ("bir_exec_step_n_PROGRAM_EQ",
``!p1 p2.
  bir_program_eq p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_step_n p1 = bir_exec_step_n p2)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
MP_TAC (Q.SPECL [`p1`, `p2`, `(T, \_ _. T)`] bir_exec_steps_GEN_PROGRAM_EQ) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_n_def,
  bir_state_COUNT_PC_ENV_ALL_STEPS]);


val bir_exec_step_n_SUBPROGRAM_EQ = store_thm ("bir_exec_step_n_SUBPROGRAM_EQ",
``!p1 p2 st c st' l n.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  (bir_exec_step_n p1 st c  = (l, n, st')) ==>
  (!l. (st'.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) ==>
  (bir_exec_step_n p2 st c = (l, n, st'))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`, `(T, \_ _. T)`] bir_exec_steps_GEN_Ended_SUBPROGRAM_EQ) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_n_TO_steps_GEN,
  bir_state_COUNT_PC_ENV_ALL_STEPS]);




(***********************)
(* Lifting it to steps *)
(***********************)

val bir_exec_steps_TERMINATES_SUBPROGRAM_EQ = store_thm ("bir_exec_steps_TERMINATES_SUBPROGRAM_EQ",
``!p1 p2 st st' ol n n'.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  bir_is_valid_pc p1 st.bst_pc ==>
  (bir_exec_steps p1 st  = BER_Ended ol n n' st') ==>
  (!l. (st'.bst_status = BST_JumpOutside l) ==>
       ~(MEM l (bir_labels_of_program p2))) ==>
  (bir_exec_steps p2 st = BER_Ended ol n n' st')``,

SIMP_TAC std_ss [bir_exec_steps_TO_bir_exec_step_n] >>
METIS_TAC [bir_exec_step_n_SUBPROGRAM_EQ]);




val bir_exec_steps_NO_TERMINATE_SUBPROGRAM = store_thm ("bir_exec_steps_NO_TERMINATE_SUBPROGRAM",
``!p1 p2 st st' ll n.
  bir_is_subprogram p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_steps p1 st = BER_Looping ll) ==>
  (bir_exec_steps p2 st = BER_Looping ll)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`, `(T, \_ _. T)`, `st`, `NONE`] bir_exec_steps_GEN_Looping_SUBPROGRAM) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_def]);



val bir_exec_steps_PROGRAM_EQ = store_thm ("bir_exec_steps_PROGRAM_EQ",
``!p1 p2.
  bir_program_eq p1 p2 ==>
  bir_is_valid_labels p2 ==>
  (bir_exec_steps p1 = bir_exec_steps p2)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p1`, `p2`, `(T, \_ _. T)`] bir_exec_steps_GEN_PROGRAM_EQ) >>
ASM_SIMP_TAC std_ss [FUN_EQ_THM, bir_exec_steps_def]);



(***********************************************)
(* Running stopped execution in larger program *)
(***********************************************)

(* This is a simple consequence of bir_exec_step_n_SUBPROGRAM *)
val bir_exec_step_n_JUMP_OUTSIDE_RECOVER = store_thm ("bir_exec_step_n_JUMP_OUTSIDE_RECOVER",
``!p1 p2 st c st' l la n'.
     bir_is_subprogram p1 p2 ==>
     bir_is_valid_labels p2 ==>
     bir_is_valid_pc p1 st.bst_pc ==>
     ~(bir_state_is_terminated st) ==>
     (bir_exec_step_n p1 st c = (l,n',st')) ==>
     (st'.bst_status = BST_JumpOutside la) ==>
     MEM la (bir_labels_of_program p2) ==>
     ~MEM la (bir_labels_of_program p1) ==>
     (bir_exec_step_n p2 st n' = (l,n', (st' with
        <|bst_status := BST_Running; bst_pc := bir_block_pc la|>)))``,

REPEAT STRIP_TAC >>
`?l2 n2 st2. bir_exec_step_n p2 st n' = (l2,n2,st2)` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p1`, `p2`, `st`, `c`] bir_exec_step_n_SUBPROGRAM) >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_jumped_outside_termination_cond_def,
  bir_state_is_terminated_def]);



val _ = export_theory();
