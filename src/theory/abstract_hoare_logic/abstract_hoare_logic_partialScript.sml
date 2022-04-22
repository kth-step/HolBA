open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

val weak_rel_steps_def = Define `
  weak_rel_steps m ms ls ms' n =
          ((n > 0 /\
           FUNPOW_OPT m.trs n ms = SOME ms' /\
           m.pc ms' IN ls) /\
           !n'.
             (n' < n /\ n' > 0 ==>
             ?ms''.
               FUNPOW_OPT m.trs n' ms = SOME ms'' /\
               ~(m.pc ms'' IN ls)
             ))`;

val weak_rel_steps_equiv = prove(``
  !m ms ls ms'.
  weak_model m ==>
  (m.weak ms ls ms' <=>
  ?n. weak_rel_steps m ms ls ms' n)
  ``,

REPEAT STRIP_TAC >>
EQ_TAC >> (
 STRIP_TAC
) >| [
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 Q.EXISTS_TAC `n` >>
 fs [weak_rel_steps_def],

 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 fs [weak_rel_steps_def] >>
 Q.EXISTS_TAC `n` >>
 REPEAT STRIP_TAC >> (
  fs []
 )
]
);

val weak_rel_steps_label = prove(``
  !m ms ls ms' n.
  weak_model m ==>
  weak_rel_steps m ms ls ms' n ==>
  m.pc ms' IN ls
  ``,

fs [weak_rel_steps_def]
);

val weak_rel_steps_smallest_exists = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' n.
   ~(weak_rel_steps m ms ls ms' n) ==>
   (n > 0) ==>
   (FUNPOW_OPT m.trs n ms = SOME ms') ==>
   (m.pc ms' IN ls) ==>
   ?n' ms''.
    n' < n /\ n' > 0 /\
    FUNPOW_OPT m.trs n' ms = SOME ms'' /\
    (m.pc ms'' IN ls) /\
    (!n''.
     (n'' < n' /\ n'' > 0 ==>
      ?ms'''. FUNPOW_OPT m.trs n'' ms = SOME ms''' /\
      ~(m.pc ms''' IN ls)))
  ``,

cheat
);

val weak_rel_steps_intermediate_labels = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' n.
  weak_rel_steps m ms ls1 ms' n ==>
  ~(weak_rel_steps m ms (ls1 UNION ls2) ms' n) ==>
  ?ms'' n'. weak_rel_steps m ms ls2 ms'' n' /\ n' < n
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
rfs [] >>
subgoal `?n' ms''.
  n' < n /\ n' > 0 /\
  FUNPOW_OPT m.trs n' ms = SOME ms'' /\
  (m.pc ms'' IN (ls1 UNION ls2)) /\
  (!n''.
   (n'' < n' /\ n'' > 0 ==>
    ?ms'''. FUNPOW_OPT m.trs n'' ms = SOME ms''' /\
    ~(m.pc ms''' IN (ls1 UNION ls2))))` >- (
 irule weak_rel_steps_smallest_exists >>
 fs [weak_rel_steps_def] >>
 Q.EXISTS_TAC `n'` >>
 REPEAT STRIP_TAC >> (
  fs []
 )
) >>
Q.EXISTS_TAC `ms''` >>
Q.EXISTS_TAC `n''` >>
fs [] >| [
 QSPECL_X_ASSUM ``!(n':num). n' < n /\ n' > 0 ==> _`` [`n''`] >>
 rfs [],

 REPEAT STRIP_TAC >>
 QSPECL_X_ASSUM ``!(n'3':num). n'3' < n'' /\ n'3' > 0 ==> _`` [`n'3'`] >>
 rfs []
]
);

val weak_rel_steps_union = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms'' n n'.
  weak_rel_steps m ms ls1 ms' n ==>
  weak_rel_steps m ms ls2 ms'' n' ==>
  n' < n ==>
  weak_rel_steps m ms (ls1 UNION ls2) ms'' n'
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
rfs [] >>
fs []
);

val weak_intermediate_labels = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms'.
  m.weak ms ls1 ms' ==>
  ~(m.weak ms (ls1 UNION ls2) ms') ==>
  ?ms''. (m.pc ms'') IN ls2 /\ m.weak ms (ls1 UNION ls2) ms''
  ``,

REPEAT STRIP_TAC >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
QSPECL_X_ASSUM ``!n. _`` [`n`] >>
IMP_RES_TAC weak_rel_steps_intermediate_labels >>
Q.EXISTS_TAC `ms''` >>
CONJ_TAC >| [
 METIS_TAC [weak_rel_steps_label],

 METIS_TAC [weak_rel_steps_union]
]
);

(* Definition of the triple *)
(* Pre and post usually have conditions on execution mode and code in memory *)
(* also post is usually a map that depends on the end state address *)
val abstract_partial_jgmt_def = Define `
  abstract_partial_jgmt m (l:'a) (ls:'a->bool) pre post =
  !ms ms'.
   ((m.pc ms) = l) ==>
   pre ms ==>
   m.weak ms ls ms' ==>
   post ms'
`;

val abstract_jgmt_imp_partial_triple =
  store_thm("abstract_jgmt_imp_partial_triple",
  ``!m l ls pre post.
    weak_model m ==>
    abstract_jgmt m l ls pre post ==>
    abstract_partial_jgmt m l ls pre post``,

FULL_SIMP_TAC std_ss [abstract_jgmt_def, abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
METIS_TAC [weak_unique_thm]
);

val weak_partial_case_rule_thm = prove(``
!m l ls pre post C1.
  abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  abstract_partial_jgmt m l ls pre post
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
METIS_TAC []
);

val weak_partial_weakening_rule_thm =
  store_thm("weak_partial_weakening_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    abstract_partial_jgmt m l ls pre1 post1 ==>
    abstract_partial_jgmt m l ls pre2 post2
  ``,

SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC weak_pc_in_thm >>
METIS_TAC [weak_pc_in_thm]
);

val weak_partial_subset_rule_thm =
 store_thm("weak_partial_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. post ms ==> (~(m.pc ms IN ls2))) ==>
    abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
    abstract_partial_jgmt m l ls1 pre post``,

REPEAT STRIP_TAC >>
rfs [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_ASSUM ``!ms ms'. _`` [`ms`, `ms'`] >>
rfs [] >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
 fs []
) >>
subgoal `?n. FUNPOW_OPT m.trs n ms = SOME ms'` >- (
 METIS_TAC [weak_model_def]
) >>
IMP_RES_TAC weak_intermediate_labels >>
QSPECL_X_ASSUM ``!ms ms'. _`` [`ms`, `ms''`] >>
rfs [] >>
METIS_TAC []
);


val weak_partial_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  abstract_partial_jgmt m l ls pre post1 ==>
  abstract_partial_jgmt m l ls pre post2 ==>
  abstract_partial_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_unique_thm]
);

(* TODO: This is introduced since negating m.weak gets weird *)
(* TODO: Still needed? *)
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

val weak_partial_seq_rule_thm = store_thm("weak_partial_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
    (!l1. (l1 IN ls1) ==>
    (abstract_partial_jgmt m l1 ls2 post post)) ==>
    abstract_partial_jgmt m l ls2 pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
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
    ((~(l IN le)) /\
    (abstract_partial_jgmt m l ({l} UNION le) (\ms. (invariant ms) /\ (C1 ms))
         (\ms.(((m.pc ms)=l) /\ (invariant ms)))))
`;
(* TODO: Preliminaries for proving partial loop rule *)
val weak_partial_loop_rule_thm = store_thm("weak_partial_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    weak_partial_loop_contract m l le invariant C1 var ==>
    abstract_partial_jgmt m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
    abstract_partial_jgmt m l le invariant post``,

cheat
);

val _ = export_theory();
