open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

(*
val weak_subset_thm = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' n.
  (n > 0 /\ (FUNPOW_OPT m.trs n ms = SOME ms') /\ m.pc ms' IN ls1 /\
   !n'.
   n' < n /\ n' > 0 ==>
   ?ms''.
       (FUNPOW_OPT m.trs n' ms = SOME ms'') /\ m.pc ms'' NOTIN ls1)
   ==>
  ?ms'' n'.
       (n' <= n /\ n' > 0 /\ (FUNPOW_OPT m.trs n' ms = SOME ms'') /\
        m.pc ms'' IN ls1 UNION ls2) /\
       !n''.
           n'' < n' /\ n'' > 0 ==>
           ?ms''.
               (FUNPOW_OPT m.trs n'' ms = SOME ms'') /\
               m.pc ms'' NOTIN ls1 UNION ls2``,

cheat
);
*)

val weak_not_union_thm = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms'.
  ~(m.weak ms (ls1 UNION ls2) ms') ==>
  ~(m.weak ms ls1 ms') /\ ~(m.weak ms ls2 ms')``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >| [
  QSPECL_X_ASSUM ``!n.
             (~(n > 0) \/ FUNPOW_OPT m.trs n ms <> SOME ms' \/
              m.pc ms' NOTIN ls1 UNION ls2) \/
             ?n'.
                 (n' < n /\ n' > 0) /\
                 !ms''.
                     FUNPOW_OPT m.trs n' ms <> SOME ms'' \/
                     m.pc ms'' IN ls1 UNION ls2`` [`n`] >> (
    FULL_SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss) []
  ) >>
  QSPECL_X_ASSUM ``!(n':num). n' < n /\ n' > 0 ==> _`` [`n'`] >>
  REV_FULL_SIMP_TAC arith_ss [] >>
  QSPECL_X_ASSUM ``!ms''. _`` [`ms''`] >>

]
cheat
);

(* Definition of the triple *)
(* Pre and post usually have conditions on execution mode and code in memory *)
(* also post is usually a map that depends on the end state address *)
val weak_partial_triple_def = Define `
  weak_partial_triple m (l:'a) (ls:'a->bool) pre post =
  !ms ms'.
   ((m.pc ms) = l) ==>
   pre ms ==>
   m.weak ms ls ms' ==>
   post ms'
`;

val weak_triple_imp_partial_triple =
  store_thm("weak_triple_imp_partial_triple",
  ``!m l ls pre post.
    weak_model m ==>
    weak_triple m l ls pre post ==>
    weak_partial_triple m l ls pre post``,

FULL_SIMP_TAC std_ss [weak_triple_def, weak_partial_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
METIS_TAC [weak_unique_thm]
);

val weak_partial_case_rule_thm = prove(``
!m l ls pre post C1.
  weak_partial_triple m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  weak_partial_triple m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  weak_partial_triple m l ls pre post
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_partial_triple_def] >>
METIS_TAC []
);

val weak_partial_weakening_rule_thm =
  store_thm("weak_partial_weakening_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    weak_partial_triple m l ls pre1 post1 ==>
    weak_partial_triple m l ls pre2 post2
  ``,

SIMP_TAC std_ss [weak_partial_triple_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC weak_pc_in_thm >>
METIS_TAC [weak_pc_in_thm]
);


(* TODO: This is introduced since negating m.weak gets weird *)
val trs_in_lblset_def = Define `
  trs_in_lblset m ms n ls =
    let
      ms'_opt = FUNPOW_OPT m.trs n ms
    in
    if IS_NONE ms'_opt
    then F
    else if m.pc (THE ms'_opt) IN ls
         then T
         else F
`;

val weak_partial_subset_rule_thm =
 store_thm("weak_partial_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. ((post ms) ==> (~((m.pc ms) IN ls2)))) ==>
    weak_partial_triple m l (ls1 UNION ls2) pre post ==>
    weak_partial_triple m l ls1 pre post``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_partial_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
(* Either execution from ms to ms' encounters ls2 along the way, or not. *)
Cases_on `?n'. n' <= n /\ n' > 0 ==> trs_in_lblset m ms n' ls2` >| [
  (* Case yes: Then there must be a first time (as in, the encounter with least amount of steps
   * taken) ls2 is encountered (needs separate proof), say after n' steps in state ms''. 
   * So, (m.pc ms'' IN ls2) and m.weak ms (ls1 UNION ls2) ms'' (since no ls1 encountered from
   * m.weak ms ls1 ms') but with
   * !ms''. m.weak ms (ls1 UNION ls2) ms'' ==> post ms'' you can then derive that post ms'', which is
   * contradicted by !ms. post ms ==> m.pc ms NOTIN ls2.  *)
  subgoal `?n''. !n'''. n''' < n'' /\ n'' > 0 ==> ~trs_in_lblset m ms n''' ls` >- (
    Q.EXISTS_TAC `n'` >>
    cheat
  ) >>
  cheat,

  (* Case no: m.weak ms ls1 ms' can be expanded to m.weak ms (ls1 UNION ls2) ms'
   * and be used with !ms''. m.weak ms (ls1 UNION ls2) ms'' ==> post ms'' to obtain
   * post ms'. *)
  FULL_SIMP_TAC std_ss [] >>
  `?n'.
   ((FUNPOW_OPT m.trs n' ms = SOME ms') /\
    m.pc ms' IN ls1 UNION ls2) /\
   !n''.
       n'' < n' ==>
       ?ms''.
	   (FUNPOW_OPT m.trs n'' ms = SOME ms'') /\
	   m.pc ms'' NOTIN ls1 UNION ls2` suffices_by (
    METIS_TAC []
  ) >>
  Q.EXISTS_TAC `n` >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss) []
  ) >>
  QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
  FULL_SIMP_TAC std_ss [trs_in_lblset_def, LET_DEF] >| [
    (* Contradiction: Cannot be NONE for n'' steps, then return to SOME for n steps *)
    cheat,

    subgoal `?ms''. FUNPOW_OPT m.trs n'' ms = SOME ms''` >- (
      (* Contradiction: Cannot be NONE for n'' steps, then return to SOME for n steps *)
      cheat
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    QSPECL_X_ASSUM ``!n'.
		     n' < n ==>
		     ?ms''.
			 (FUNPOW_OPT m.trs n' ms = SOME ms'') /\ m.pc ms'' NOTIN ls1`` [`n''`] >>
    REV_FULL_SIMP_TAC std_ss []
  ]
]
);


val weak_partial_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  weak_partial_triple m l ls pre post1 ==>
  weak_partial_triple m l ls pre post2 ==>
  weak_partial_triple m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_partial_triple_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_unique_thm]
);


val weak_partial_seq_rule_thm = store_thm("weak_partial_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    weak_partial_triple m l (ls1 UNION ls2) pre post ==>
    (!l1. (l1 IN ls1) ==>
    (weak_partial_triple m l1 ls2 post post)) ==>
    weak_partial_triple m l ls2 pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_partial_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms ms'.
		 (m.pc ms = l) ==>
		 pre ms ==>
		 m.weak ms (ls1 UNION ls2) ms' ==>
		 post ms'`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
(* Case split on whether ls1 was visited before ms'. *)
Cases_on `?n'. n' <= n /\ n' > 0 ==> trs_in_lblset m ms n' ls1` >| [
  (* Case yes: Then there must be a first time (as in, the encounter with least amount of steps
   * taken) ls1 is encountered (needs separate proof), say after n' steps in state ms''. 
   * So, (m.pc ms'' IN ls1) and m.weak ms (ls1 UNION ls2) ms'' (since no ls2 encountered from
   * m.weak ms ls2 ms') but with
   * !l1.
             l1 IN ls1 ==>
             !ms ms'.
                 (m.pc ms = l1) ==>
                 post ms ==>
                 m.weak ms ls2 ms' ==>
                 post ms' you can then derive that post ms'.  *)
  cheat,

  (* Case no: m.weak ms ls1 ms' can be expanded to m.weak ms (ls1 UNION ls2) ms'
   * and be used with !ms''. m.weak ms (ls1 UNION ls2) ms'' ==> post ms'' to obtain
   * post ms'. *)
  cheat
]
);



val weak_partial_loop_contract_def = Define `
  weak_partial_loop_contract m l le invariant C1 var =
    (~(l IN le)) /\
    (weak_partial_triple m l ({l} UNION le) (\ms. (invariant ms) /\ (C1 ms))
         (\ms.(((m.pc ms)=l) /\ (invariant ms))))
`;
(* TODO: Preliminaries for proving partial loop rule *)
val weak_partial_loop_rule_thm = store_thm("weak_partial_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    weak_partial_loop_contract m l le invariant C1 var ==>
    weak_partial_triple m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
    weak_partial_triple m l le invariant post``,

cheat
);

val _ = export_theory();
