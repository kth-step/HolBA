open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_programTheory;
open llistTheory wordsLib;

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
  ``!p st n1 n2. bir_state_is_terminated (bir_exec_infinite_steps_fun p st n1) ==>
                 (!n2. (n1 <= n2) ==> (bir_exec_infinite_steps_fun p st n2 =
                                       bir_exec_infinite_steps_fun p st n1))``,

REPEAT STRIP_TAC >>
`?c. n2 = n1 + c` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
ASM_SIMP_TAC std_ss [GSYM bir_exec_infinite_steps_fun_ADD,
  bir_exec_infinite_steps_fun_TERMINATED_0]);


(***************************************)
(* bir_exec_infinite_steps_COUNT_STEPS *)
(***************************************)

val bir_exec_infinite_steps_COUNT_STEPS_UNFOLD = store_thm (
  "bir_exec_infinite_steps_COUNT_STEPS_UNFOLD",
  ``!p st.
    (bir_exec_infinite_steps_COUNT_STEPS p st =
     if bir_state_is_terminated st then SOME 0 else
     OPT_NUM_SUC (bir_exec_infinite_steps_COUNT_STEPS p (bir_exec_step_state p st)))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def,
  whileTheory.OLEAST_def] >>
REPEAT GEN_TAC >>
Q.ABBREV_TAC `P = \st i. bir_state_is_terminated (bir_exec_infinite_steps_fun p st i)` >>
`(bir_state_is_terminated st = P st 0) /\ (!i. (P (bir_exec_step_state p st) i = P st (SUC i)))` by (
  Q.UNABBREV_TAC `P` >>
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>
ASM_SIMP_TAC std_ss [] >>
REPEAT (POP_ASSUM (K ALL_TAC)) >>
Tactical.REVERSE COND_CASES_TAC >- (
  FULL_SIMP_TAC std_ss [OPT_NUM_SUC_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `P st 0` >- (
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


val bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWRS = store_thm (
  "bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWRS",
  ``(!p st.
    bir_state_is_terminated st ==>
    (bir_exec_infinite_steps_COUNT_STEPS p st = SOME 0)) /\

   (!p st.
    ~(bir_state_is_terminated st) ==>
    (bir_exec_infinite_steps_COUNT_STEPS p st =
    (OPT_NUM_SUC (bir_exec_infinite_steps_COUNT_STEPS p (bir_exec_step_state p st)))))``,

CONJ_TAC >> SIMP_TAC std_ss [Once bir_exec_infinite_steps_COUNT_STEPS_UNFOLD]);


val bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE = store_thm ("bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE",
  ``(bir_exec_infinite_steps_COUNT_STEPS p state = NONE) <=>
    (!n. ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n)))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_def]);


val bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME = store_thm ("bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME",
  ``(bir_exec_infinite_steps_COUNT_STEPS p state = SOME i) <=>
    ((bir_state_is_terminated (bir_exec_infinite_steps_fun p state i)) /\
     (!n. n < i ==> ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n))))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_def] >>
Q.ABBREV_TAC `P = (\state i. bir_state_is_terminated ((bir_exec_infinite_steps_fun p state i)))` >>
ASM_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC) >>
EQ_TAC >> STRIP_TAC >| [
  METIS_TAC[whileTheory.LEAST_EXISTS_IMP],
  METIS_TAC[bitTheory.LEAST_THM]
]);


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
 ``!p st n. bir_exec_steps_observe_llist p st NONE =
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
(* bir_exec_steps_opt                                          *)
(***************************************************************)

val bir_exec_steps_opt_REWR_TERMINATED = store_thm ("bir_exec_steps_opt_REWR_TERMINATED",
  ``!p st max_steps.
    bir_state_is_terminated st ==>
    (bir_exec_steps_opt p st max_steps = ([||], SOME (0, st)))``,

SIMP_TAC std_ss [bir_exec_steps_opt_def, bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWRS,
  OPT_NUM_MIN_SOME0, bir_exec_steps_observe_llist_0, LET_DEF,
  bir_exec_infinite_steps_fun_REWRS]);


val bir_exec_steps_opt_no_steps = store_thm ("bir_exec_steps_opt_no_steps",
  ``!p st.
    (bir_exec_steps_opt p st (SOME 0) = ([||], SOME (0, st)))``,

SIMP_TAC std_ss [bir_exec_steps_opt_def,
  OPT_NUM_MIN_SOME0, LET_THM, bir_exec_steps_observe_llist_0,
  bir_exec_infinite_steps_fun_REWRS]);


val bir_exec_steps_opt_REWR_NOT_TERMINATED = store_thm ("bir_exec_steps_opt_REWR_NOT_TERMINATED",
  ``!p st max_steps.
    ~(bir_state_is_terminated st) ==>
    (bir_exec_steps_opt p st max_steps =
      (if (max_steps = SOME 0) then ([||], SOME (0, st)) else (
      (let (fe, st') = bir_exec_step p st in
       let (ll, fst_opt) = (bir_exec_steps_opt p st' (OPT_NUM_PRE max_steps)) in
       ((OPT_LCONS fe ll),
          OPTION_MAP (\ (i, st). (SUC i, st)) fst_opt)))))``,

REPEAT GEN_TAC >>
Cases_on `max_steps = SOME 0` >- ASM_SIMP_TAC std_ss [bir_exec_steps_opt_no_steps] >>
`?fe st'. bir_exec_step p st = (fe, st')` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [bir_exec_steps_opt_def, bir_exec_infinite_steps_COUNT_STEPS_TERMINATED_REWRS] >>

ASM_SIMP_TAC std_ss [bir_exec_step_state_def, OPT_NUM_MIN_OPT_NUM_SUC, LET_THM,
  bir_exec_steps_observe_llist_OPT_NUM_SUC] >>
Q.ABBREV_TAC `no = OPT_NUM_MIN (OPT_NUM_PRE max_steps)
        (bir_exec_infinite_steps_COUNT_STEPS p st')` >>
Cases_on `no` >> (
  ASM_SIMP_TAC std_ss [OPT_NUM_SUC_def, bir_exec_infinite_steps_fun_REWRS,
    bir_exec_step_state_def]
));


val bir_exec_steps_opt_EQ_NONE = store_thm ("bir_exec_steps_opt_EQ_NONE",
  ``((bir_exec_steps_opt p state mo) = (ll, NONE)) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (mo = NONE) /\ (bir_exec_infinite_steps_COUNT_STEPS p state = NONE))``,

Cases_on `mo` >> Cases_on `bir_exec_infinite_steps_COUNT_STEPS p state` >> (
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_opt_def, LET_DEF, OPT_NUM_MIN_REWRS]
));


val bir_exec_steps_opt_EQ_NONE_SND = store_thm ("bir_exec_steps_opt_EQ_NONE_SND",
  ``(SND (bir_exec_steps_opt p state mo) = NONE) <=>
    (
     (mo = NONE) /\ (bir_exec_infinite_steps_COUNT_STEPS p state = NONE))``,

Cases_on `mo` >> Cases_on `bir_exec_infinite_steps_COUNT_STEPS p state` >> (
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exec_steps_opt_def, LET_DEF, OPT_NUM_MIN_REWRS]
));


val bir_exec_steps_opt_EQ_SOME = store_thm ("bir_exec_steps_opt_EQ_SOME",
  ``!p state mo ll c state'.
    (bir_exec_steps_opt p state mo = (ll, SOME (c, state'))) <=>
    ((ll = bir_exec_steps_observe_llist p state (SOME c)) /\
     (case mo of NONE => (bir_state_is_terminated state')
               | SOME m => ((c <= m) /\ ((c < m) ==> (bir_state_is_terminated state')))) /\
     (state' = bir_exec_infinite_steps_fun p state c) /\
     (!n. n < c ==> ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n))))``,

REPEAT GEN_TAC >>
EQ_TAC >- (
  SIMP_TAC std_ss [bir_exec_steps_opt_def, LET_DEF] >>
  Cases_on ` OPT_NUM_MIN mo (bir_exec_infinite_steps_COUNT_STEPS p state)` >> (
    ASM_SIMP_TAC std_ss []
  ) >>
  STRIP_TAC >> REPEAT (BasicProvers.VAR_EQ_TAC) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `(bir_exec_infinite_steps_COUNT_STEPS p state)` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE, OPT_NUM_MIN_REWRS]
  ) >>
  rename1 `bir_exec_infinite_steps_COUNT_STEPS _ _ = SOME cc2` >>
  `(c <= cc2) /\ (c <> cc2 ==> (mo = SOME c)) /\ (!c'. (mo = SOME c') ==> c <= c')` by (
     Cases_on `mo` >>
     FULL_SIMP_TAC arith_ss [OPT_NUM_MIN_REWRS] >>
     BasicProvers.VAR_EQ_TAC >>
     SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF]
  ) >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >>
  Cases_on `mo` >> (
    FULL_SIMP_TAC arith_ss []
  ) >>
  STRIP_TAC >>
  rename1 `c < cc1` >>
  `cc1 <> c` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss []
) >- (
  SIMP_TAC std_ss [bir_exec_steps_opt_def, LET_DEF] >>
  STRIP_TAC >> REPEAT (BasicProvers.VAR_EQ_TAC) >>
  Cases_on `mo` >- (
    FULL_SIMP_TAC arith_ss [OPT_NUM_MIN_REWRS] >>
    `bir_exec_infinite_steps_COUNT_STEPS p state = SOME c` by
      METIS_TAC[bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >>
    ASM_SIMP_TAC std_ss []
  ) >>
  rename1 `OPT_NUM_MIN (SOME cc1) _` >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS p state` >- (
    ASM_SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
    `cc1 = c` by DECIDE_TAC >>
    ASM_REWRITE_TAC[]
  ) >>
  rename1 `OPT_NUM_MIN (SOME cc1) (SOME cc2)` >>
  ASM_SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
  `MIN cc1 cc2 = c` suffices_by SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >>
  `~(cc2 < c)` by METIS_TAC[] >>
  Cases_on `c < cc1` >| [
    `~(c < cc2)` by METIS_TAC[] >>
    `c = cc2` by DECIDE_TAC >>
    FULL_SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF],

    FULL_SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF]
  ]
));



(***************************************************************)
(* bir_exec_steps_n                                            *)
(***************************************************************)

val bir_exec_step_n_EQ_THM = store_thm ("bir_exec_step_n_EQ_THM",
  ``((bir_exec_step_n p state n = (l, c, state'))) <=>
    ((l = bir_exec_steps_observe_list p state c) /\
     (c <= n) /\ (c < n ==> bir_state_is_terminated state') /\
     (state' = bir_exec_infinite_steps_fun p state c) /\
     (!n.
        n < c ==>
        ~bir_state_is_terminated
           (bir_exec_infinite_steps_fun p state n)))``,

`?l' c' st'. bir_exec_steps_opt p state (SOME n) = (l',SOME (c',st'))` by (
  `~((SND (bir_exec_steps_opt p state (SOME n))) = NONE)` by (
    SIMP_TAC std_ss [bir_exec_steps_opt_EQ_NONE_SND]
  ) >>
  Cases_on `bir_exec_steps_opt p state (SOME n)` >>
  rename1 `_ = (l', xx)` >>
  Cases_on `xx` >> FULL_SIMP_TAC std_ss [] >>
  rename1 `_ = (l', SOME xx)` >>
  Cases_on `xx` >>
  SIMP_TAC std_ss []
) >>

ASM_SIMP_TAC std_ss [bir_exec_step_n_def, LET_THM] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_opt_EQ_SOME, bir_exec_steps_observe_llist_toList_SOME] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
Cases_on `c = c'` >- (
   ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
   METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss [] >>
CCONTR_TAC >>
Cases_on `~(bir_state_is_terminated state')` >- (
  FULL_SIMP_TAC std_ss [] >>
  `(c' < c) /\ (c = n)` by DECIDE_TAC >>
  METIS_TAC[]
) >>
FULL_SIMP_TAC arith_ss [] >> REPEAT BasicProvers.VAR_EQ_TAC >>

`~(c < c')` by METIS_TAC[] >>
`(c' < c) /\ (c' < n)` by DECIDE_TAC >>
METIS_TAC[]);


val bir_exec_step_n_combine = store_thm ("bir_exec_step_n_combine",
  ``!p state0 state1 state2 n1 n2 l1 l2 c1 c2.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_step_n p state1 n2 = (l2, c2, state2)) ==>
    (bir_exec_step_n p state0 (n1 + n2) = (l1++l2, c1+c2, state2))``,

SIMP_TAC arith_ss [bir_exec_step_n_EQ_THM,
  GSYM bir_exec_steps_observe_list_ADD,
  bir_exec_infinite_steps_fun_ADD] >>
REPEAT STRIP_TAC >- (
  Cases_on `c1 < n1` >- (
    FULL_SIMP_TAC bool_ss [GSYM bir_exec_infinite_steps_fun_ADD,
      bir_exec_infinite_steps_fun_TERMINATED_0, combinTheory.K_DEF]
  ) >>
  `c1 = n1` by DECIDE_TAC >> BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC std_ss []
) >- (
  rename1 `n < _ + _` >>
  Cases_on `n < c1` >- METIS_TAC [] >>
  `?m. n = c1 + m` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS, arithmeticTheory.NOT_LESS] >>
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC[]
));


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
(* bir_exec_steps                                              *)
(***************************************************************)

val bir_exec_steps_EQ_NONE = store_thm ("bir_exec_steps_EQ_NONE",
  ``(bir_exec_steps p state = (ll, NONE)) <=>
    ((ll = bir_exec_steps_observe_llist p state NONE) /\
     (bir_exec_infinite_steps_COUNT_STEPS p state = NONE))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_NONE]);


val bir_exec_steps_EQ_SOME = store_thm ("bir_exec_steps_EQ_SOME",
  ``((bir_exec_steps p state = (ll, SOME (c, state')))) <=>
    ((ll = bir_exec_steps_observe_llist p state (SOME c)) /\
     bir_state_is_terminated state' /\
     (state' = bir_exec_infinite_steps_fun p state c) /\
     (!n. n < c ==> ~(bir_state_is_terminated (bir_exec_infinite_steps_fun p state n))))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_EQ_SOME]);


val bir_exec_steps_REWR_TERMINATED = store_thm ("bir_exec_steps_REWR_TERMINATED",
  ``bir_state_is_terminated state ==>
    (bir_exec_steps p state = ([||], SOME (0, state)))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_REWR_TERMINATED]);


val bir_exec_steps_REWR_NOT_TERMINATED = store_thm ("bir_exec_steps_REWR_NOT_TERMINATED",
  ``~bir_state_is_terminated state ==>
    (bir_exec_steps p state =
       let (fe, state') = bir_exec_step p state in
       let (ll,fst_opt) = bir_exec_steps p state' in
       ((OPT_LCONS fe ll),
        OPTION_MAP (\ (i,st). (SUC i, st)) fst_opt))``,

SIMP_TAC std_ss [bir_exec_steps_def, bir_exec_steps_opt_REWR_NOT_TERMINATED,
  OPT_NUM_PRE_def, LET_THM]);


val bir_exec_steps_combine = store_thm ("bir_exec_steps_combine",
  ``!p state0 n1 state1 c1 l1.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_steps p state0 =
       (let (ll2, sto) = bir_exec_steps p state1 in
        (LAPPEND (fromList l1) ll2, case sto of
         | NONE => NONE
         | SOME (c2, state2) => SOME (c1+c2, state2))))``,

REPEAT STRIP_TAC >>
`?ll2 sto. (bir_exec_steps p state1) = (ll2, sto)` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, LET_THM,
  bir_exec_steps_observe_list_fromList] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
Cases_on `sto` >- (
  FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_NONE, bir_exec_steps_observe_llist_NONE_ADD,
    bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE, bir_exec_infinite_steps_fun_ADD] >>
  GEN_TAC >>
  Cases_on `n < c1` >- METIS_TAC[] >>
  METIS_TAC[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_EXISTS]
) >- (
  rename1 `_ = (_, SOME x)` >> Cases_on `x` >> rename1 `_ = (_, SOME (c2, state2))` >>
  FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_SOME, pairTheory.pair_case_thm,
    bir_exec_steps_observe_llist_SOME_ADD, bir_exec_infinite_steps_fun_ADD] >>
  REPEAT BasicProvers.VAR_EQ_TAC >> FULL_SIMP_TAC std_ss [] >>
  GEN_TAC >>
  Cases_on `n < c1` >- METIS_TAC[] >>
  `?m. n = c1 + m` by METIS_TAC[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_EXISTS] >>
  ASM_SIMP_TAC arith_ss []
));



val bir_exec_steps_combine_GUARD = store_thm ("bir_exec_steps_combine_GUARD",
  ``!p state0 n1 state1 c1 l1.
    (bir_exec_step_n p state0 n1 = (l1, c1, state1)) ==>
    (bir_exec_steps p state0 =
       (if c1 < n1 then (fromList l1, SOME (c1, state1)) else (
       (let (ll2, sto) = bir_exec_steps p state1 in
       (LAPPEND (fromList l1) ll2), case sto of
         | NONE => NONE
         | SOME (c2, state2) => SOME (c1+c2, state2)))))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `state0`, `n1`] bir_exec_steps_combine) >>
ASM_SIMP_TAC std_ss [] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>
Cases_on `c1 < n1` >> ASM_REWRITE_TAC[] >>
`bir_state_is_terminated state1` by (
   FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM]
) >>
FULL_SIMP_TAC std_ss [bir_exec_steps_REWR_TERMINATED, LET_THM,
  LAPPEND_NIL_2ND, pairTheory.pair_case_thm]);


val _ = export_theory();
