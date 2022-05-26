open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logic_auxTheory abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

Definition weak_rel_steps_def:
 weak_rel_steps m ms ls ms' n =
  ((n > 0 /\
   FUNPOW_OPT m.trs n ms = SOME ms' /\
   m.pc ms' IN ls) /\
   !n'.
     (n' < n /\ n' > 0 ==>
     ?ms''.
       FUNPOW_OPT m.trs n' ms = SOME ms'' /\
       ~(m.pc ms'' IN ls)
     ))
End

Theorem weak_rel_steps_imp:
 !m ms ls ms' n.
 weak_model m ==>
 (weak_rel_steps m ms ls ms' n ==>
  m.weak ms ls ms')
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
qexists_tac `n` >>
fs [weak_rel_steps_def]
QED

Theorem weak_rel_steps_equiv:
 !m ms ls ms'.
 weak_model m ==>
 (m.weak ms ls ms' <=>
 ?n. weak_rel_steps m ms ls ms' n)
Proof
rpt strip_tac >>
EQ_TAC >> (
 strip_tac
) >| [
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 qexists_tac `n` >>
 fs [weak_rel_steps_def],

 metis_tac [weak_rel_steps_imp]
]
QED

Theorem weak_rel_steps_label:
 !m ms ls ms' n.
 weak_model m ==>
 weak_rel_steps m ms ls ms' n ==>
 m.pc ms' IN ls
Proof
fs [weak_rel_steps_def]
QED

Theorem weak_rel_steps_to_FUNPOW_OPT_LIST:
 !m ms ls ms' n.
 weak_model m ==>
 (weak_rel_steps m ms ls ms' n <=>
  n > 0 /\
  ?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) /\
            INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (PRE n, ms'))
Proof
rpt strip_tac >>
EQ_TAC >> (
 rpt strip_tac
) >| [
 fs [weak_rel_steps_def],

 fs [weak_rel_steps_def] >>
 IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS_exact >>
 fs [] >>
 fs [INDEX_FIND_EQ_SOME_0, FUNPOW_OPT_LIST_EQ_SOME] >>
 rpt strip_tac >| [
  rw [] >>
  fs [EL_LAST_APPEND],

  QSPECL_X_ASSUM ``!n'. n' < n /\ n' > 0 ==> m.pc (EL n' (ms::SNOC ms' l)) NOTIN ls`` [`SUC j'`] >>
  gs [listTheory.SNOC_APPEND]
 ],

 fs [FUNPOW_OPT_LIST_EQ_SOME, INDEX_FIND_EQ_SOME_0, weak_rel_steps_def] >>
 rpt strip_tac >| [
  fs [listTheory.LAST_DEF] >>
  subgoal `ms_list <> []` >- (
   Cases_on `ms_list` >> (
    fs []
   )
  ) >>
  rw [] >>
  metis_tac [listTheory.LAST_EL],

  QSPECL_X_ASSUM ``!j'. j' < PRE n ==> m.pc (EL j' ms_list) NOTIN ls`` [`PRE n'`] >>
  gs [] >>
  `EL n' (ms::ms_list) = EL (PRE n') ms_list` suffices_by (
   strip_tac >>
   fs []
  ) >>
  irule rich_listTheory.EL_CONS >>
  fs []
 ]
]
QED


(* If ms and ms' are not related by weak transition to ls for n transitions,
 * but if taking n transitions from ms takes you to ms' with a label in ls,
 * then there has to exist an ms'' and a *smallest* n' such that the label of
 * ms'' is in ls. *)
(* TODO: Lemmatize further *)
Theorem weak_rel_steps_smallest_exists:
 !m.
 weak_model m ==>
 !ms ls ms' n.
  ~(weak_rel_steps m ms ls ms' n) ==>
  n > 0 ==>
  FUNPOW_OPT m.trs n ms = SOME ms' ==>
  m.pc ms' IN ls ==>
  ?n' ms''.
   n' < n /\ n' > 0 /\
   FUNPOW_OPT m.trs n' ms = SOME ms'' /\
   m.pc ms'' IN ls /\
   (!n''.
    (n'' < n' /\ n'' > 0 ==>
     ?ms'''. FUNPOW_OPT m.trs n'' ms = SOME ms''' /\
     ~(m.pc ms''' IN ls)))
Proof
rpt strip_tac >>
fs [weak_rel_steps_def] >>
subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list)` >- (
 IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS >>
 QSPECL_X_ASSUM ``!n'. n' <= n ==> ?l. FUNPOW_OPT_LIST m.trs n' ms = SOME l`` [`n`] >>
 fs [] >>
 Cases_on `n` >- (
  fs [FUNPOW_OPT_LIST_def]
 ) >>
 qexists_tac `DROP 1 l` >>
 fs [FUNPOW_OPT_LIST_EQ_SOME] >>
 QSPECL_X_ASSUM ``!n'. n' <= SUC n'' ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' l)`` [`0`] >>
 fs [FUNPOW_OPT_def] >>
 Cases_on `l` >> (
  fs []
 )
) >>
subgoal `?i ms''. INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (i, ms'')` >- (
 (* OK: There is at least ms', possibly some earlier encounter of ls *)
 irule INDEX_FIND_MEM >>
 qexists_tac `ms'` >>
 fs [listTheory.MEM_EL] >>
 qexists_tac `PRE n` >>
 CONJ_TAC >| [
  IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
  fs [],

  REWRITE_TAC [Once EQ_SYM_EQ] >>
  irule FUNPOW_OPT_LIST_EL >>
  fs [] >>
  subgoal `?ms''. m.trs ms = SOME ms''` >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' (ms::ms_list))`` [`1`] >>
   fs [FUNPOW_OPT_def]
  ) >>
  qexists_tac `m.trs` >>
  qexists_tac `PRE n` >>
  qexists_tac `ms''` >>
  fs [] >>
  CONJ_TAC >| [
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   metis_tac [FUNPOW_OPT_PRE],

   metis_tac [FUNPOW_OPT_LIST_FIRST]
  ]
 ]
) >>
qexists_tac `SUC i` >>
qexists_tac `ms''` >>
fs [] >>
subgoal `?ms'''. FUNPOW_OPT m.trs n' ms = SOME ms'''` >- (
 metis_tac [FUNPOW_OPT_prev_EXISTS]
) >>
rpt strip_tac >| [
 (* i < n since i must be at least n', since INDEX_FIND at least must have found ms''',
  * if not any earlier encounter *)
 fs [INDEX_FIND_EQ_SOME_0] >>
 Cases_on `n' < (SUC i)` >| [
  (* Contradiction: ms''' occurs earlier than the first encounter of ls found by INDEX_FIND *)
  subgoal `m.pc (EL (PRE n') ms_list) NOTIN ls` >- (
   fs []
  ) >>
  subgoal `(EL (PRE n') ms_list) = ms'''` >- (
   subgoal `(EL n' (ms::ms_list)) = ms'''` >- (
    metis_tac [FUNPOW_OPT_LIST_EL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
   ) >>
   metis_tac [rich_listTheory.EL_CONS, arithmeticTheory.GREATER_DEF]
  ) >>
  fs [],

  fs []
 ],

 fs [INDEX_FIND_EQ_SOME_0, FUNPOW_OPT_LIST_EQ_SOME],

 fs [INDEX_FIND_EQ_SOME],

 subgoal `n'' < n` >- (
  fs [INDEX_FIND_EQ_SOME_0] >>
  IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
  fs []
 ) >>
 subgoal `?ms''''. FUNPOW_OPT m.trs n'' ms = SOME ms''''` >- (
  metis_tac [FUNPOW_OPT_LIST_EL_SOME, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
 ) >>
 subgoal `(EL (PRE n'') ms_list) = ms''''` >- (
  irule FUNPOW_OPT_LIST_EL >>
  subgoal `?ms'''''. m.trs ms = SOME ms'''''` >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' (ms::ms_list))`` [`1`] >>
   fs [FUNPOW_OPT_def]
  ) >>
  qexists_tac `m.trs` >>
  qexists_tac `PRE n` >>
  qexists_tac `ms'''''` >>
  fs [] >>
  rpt CONJ_TAC >| [
   irule arithmeticTheory.PRE_LESS_EQ >>
   fs [],

   metis_tac [FUNPOW_OPT_PRE],

   subgoal `n > 0` >- (
    fs []
   ) >>
   metis_tac [FUNPOW_OPT_LIST_PRE]
  ]
 ) >>
 fs [INDEX_FIND_EQ_SOME_0] >>
 rw []
]
QED

Theorem weak_rel_steps_intermediate_labels:
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' n.
  weak_rel_steps m ms ls1 ms' n ==>
  ~(weak_rel_steps m ms (ls1 UNION ls2) ms' n) ==>
  ?ms'' n'. weak_rel_steps m ms ls2 ms'' n' /\ n' < n
Proof
rpt strip_tac >>
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
 qexists_tac `n'` >>
 rpt strip_tac >> (
  fs []
 )
) >>
qexists_tac `ms''` >>
qexists_tac `n''` >>
fs [] >| [
 QSPECL_X_ASSUM ``!(n':num). n' < n /\ n' > 0 ==> _`` [`n''`] >>
 rfs [],

 rpt strip_tac >>
 QSPECL_X_ASSUM ``!(n'3':num). n'3' < n'' /\ n'3' > 0 ==> _`` [`n'3'`] >>
 rfs []
]
QED

Theorem weak_rel_steps_union:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms'' n n'.
 weak_rel_steps m ms ls1 ms' n ==>
 weak_rel_steps m ms ls2 ms'' n' ==>
 n' < n ==>
 weak_rel_steps m ms (ls1 UNION ls2) ms'' n'
Proof
rpt strip_tac >>
fs [weak_rel_steps_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
rfs [] >>
fs []
QED

Theorem weak_intermediate_labels:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'.
 m.weak ms ls1 ms' ==>
 ~(m.weak ms (ls1 UNION ls2) ms') ==>
 ?ms''. (m.pc ms'') IN ls2 /\ m.weak ms (ls1 UNION ls2) ms''
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
QSPECL_X_ASSUM ``!n. _`` [`n`] >>
IMP_RES_TAC weak_rel_steps_intermediate_labels >>
qexists_tac `ms''` >>
CONJ_TAC >| [
 metis_tac [weak_rel_steps_label],

 metis_tac [weak_rel_steps_union]
]
QED

Theorem weak_rel_steps_unique:
 !m.
 weak_model m ==>
 !ms ls ms' ms'' n n'.
 weak_rel_steps m ms ls ms' n ==>
 weak_rel_steps m ms ls ms'' n' ==>
 (ms' = ms'' /\ n = n')
Proof
rpt strip_tac >| [
 metis_tac [weak_rel_steps_imp, weak_unique_thm],

 fs [weak_rel_steps_def] >>
 CCONTR_TAC >>
 Cases_on `n < n'` >- (
  QSPECL_X_ASSUM ``!n''. _`` [`n`] >>
  rfs []
 ) >>
 QSPECL_X_ASSUM ``!n'.
                  n' < n /\ n' > 0 ==>
                  ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls`` [`n'`] >>
 rfs []
]
QED

(* If weak transition to ls connects ms to ms' via n transitions, then if for all
 * numbers of transitions n'<n goes to ms'', weak transition to ls connects ms''
 * to ms' in n-n' steps *)
(*
val weak_rel_steps_intermediate_start = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' ms'' n n'.
  n' < n ==>
  weak_rel_steps m ms ls ms' n ==>
  FUNPOW_OPT m.trs n' ms = SOME ms'' ==>
  weak_rel_steps m ms'' ls ms' (n - n')
  ``,

rpt strip_tac >>
fs [weak_rel_steps_def] >>
Cases_on `n'` >- (
 fs [FUNPOW_OPT_REWRS]
) >>
rpt strip_tac >| [
 irule FUNPOW_OPT_INTER >>
 qexists_tac `ms` >>
 qexists_tac `SUC n''` >>
 fs [],

 QSPECL_X_ASSUM ``!n'. _`` [`SUC n'' + n'`] >>
 rfs [] >>
 metis_tac [FUNPOW_OPT_INTER]
]
);
*)

(* If weak transition to ls connects ms to ms' via n transitions, and ms'' to ms'
 * via n-n' transitions, then if for all non-zero transitions n'' lower than n-n'
 * ls' is not encountered, then
 * weak transition to (ls' UNION ls) connects ms'' to ms' via n-n' transitions. *)
(*
val weak_rel_steps_superset_after = prove(``
  !m.
  weak_model m ==>
  !ms ls ls' ms' n.
  weak_rel_steps m ms ls ms' n ==>
(* Note: this is exactly the second conjunct of weak_rel_steps *)
  (!n'. n' < n /\ n' > 0 ==> (?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls')) ==>
(* TODO: This formulation also possible (end point must now also be in ls'):
  weak_rel_steps m ms ls' ms' n' ==>
*)
  weak_rel_steps m ms (ls UNION ls') ms' n
  ``,

rpt strip_tac >>
fs [weak_rel_steps_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
rfs [] >>
fs []
);
*)

Theorem weak_rel_steps_intermediate_labels2:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms'' n n'.
 weak_rel_steps m ms ls2 ms' n ==>
 ~(weak_rel_steps m ms (ls1 UNION ls2) ms' n) ==>
 weak_rel_steps m ms (ls1 UNION ls2) ms'' n' ==>
 ?n''. weak_rel_steps m ms'' ls2 ms' n'' /\ n'' < n
Proof
rpt strip_tac >>
subgoal `weak_rel_steps m ms (ls1 UNION ls2) ms'' n' /\ n' < n` >- (
 subgoal `?ms'' n'. weak_rel_steps m ms (ls1 UNION ls2) ms'' n' /\ n' < n` >- (
  metis_tac [weak_rel_steps_intermediate_labels, weak_rel_steps_union, pred_setTheory.UNION_COMM]
 ) >>
 metis_tac [weak_rel_steps_unique]
) >>
fs [] >>
fs [weak_rel_steps_def] >>
rfs [] >> (
 qexists_tac `n - n'` >>
 subgoal `FUNPOW_OPT m.trs (n - n') ms'' = SOME ms'` >- (
  metis_tac [FUNPOW_OPT_split2, arithmeticTheory.GREATER_DEF]
 ) >>
 fs [] >>
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n'.
           n' < n /\ n' > 0 ==>
           ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n' + n'3'`] >>
 subgoal `n' + n'3' < n` >- (
  fs []
 ) >>
 subgoal `n' + n'3' > 0` >- (
  fs []
 ) >>
 fs [] >>
 qexists_tac `ms'3'` >>
 fs [] >>
 metis_tac [FUNPOW_OPT_INTER, arithmeticTheory.ADD_SYM]
)
QED

Theorem weak_rel_steps_intermediate_labels3:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms'' n n'.
 weak_rel_steps m ms ls1 ms' n ==>
 weak_rel_steps m ms (ls2 UNION ls1) ms'' n' ==>
 n' < n ==>
 m.pc ms'' IN ls2
Proof
rpt strip_tac >>
fs [weak_rel_steps_def] >>
QSPECL_X_ASSUM ``!n'.
                 n' < n /\ n' > 0 ==>
                 ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'`] >>
rfs []
QED

Theorem weak_intermediate_labels2:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms''.
 m.weak ms ls2 ms' ==>
 ~(m.weak ms (ls1 UNION ls2) ms') ==>
 m.weak ms (ls1 UNION ls2) ms'' ==>
 m.weak ms'' ls2 ms'
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
metis_tac [weak_rel_steps_intermediate_labels2]
QED

(*
val weak_rel_steps_FILTER_inter = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' i i' i'' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' (LENGTH ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  EL i' ms_list = EL i (FILTER (\ms. m.pc ms = l) ms_list) ==>
  EL i'' ms_list = EL (i+1) (FILTER (\ms. m.pc ms = l) ms_list) ==>
  i < LENGTH ms_list' - 1 ==>
  FUNPOW_OPT_LIST m.trs (LENGTH ms_list) ms = SOME (ms::ms_list) ==>
  weak_rel_steps m (EL i ms_list') ({l} UNION ls) (EL (i + 1) ms_list') (i'' - i')
  ``,

rpt strip_tac >>
fs [FUNPOW_OPT_LIST_EQ_SOME] >>
(* TODO: Problem is, EL i' ms_list and EL i'' ms_list may not be unique in ms_list *)
cheat
);
*)

(*
val weak_rel_steps_FILTER_end = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' i i'' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' (LENGTH ms_list) ==>
  FUNPOW_OPT_LIST m.trs (LENGTH ms_list) ms = SOME (ms::ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  i < LENGTH ms_list' - 1 ==>
  EL i'' ms_list = EL (i+1) (FILTER (\ms. m.pc ms = l) ms_list) ==>
  weak_rel_steps m (EL (i + 1) ms_list') ls ms' (LENGTH ms_list - SUC i'')
  ``,

rpt strip_tac >>
irule weak_rel_steps_intermediate_start >>
fs [] >>
CONJ_TAC >| [
 (* TODO: SUC i'' < LENGTH ms_list from main proof goal? *)
 cheat,

 qexists_tac `ms` >>
 fs [] >>
 (* TODO: Should be OK if we have SUC i'' < LENGTH ms_list *)
 cheat
]
);
*)
(*
val weak_rel_steps_FILTER_NOTIN_end = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' n n' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' n ==>
  l NOTIN ls ==>
  FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list) = EL n' ms_list ==>
  SUC n' < n
  ``,

rpt strip_tac >>
(* TODO: Unclear? *)
cheat
);
*)


Definition abstract_partial_jgmt_def:
 abstract_partial_jgmt m (l:'a) (ls:'a->bool) pre post =
 !ms ms'.
  ((m.pc ms) = l) ==>
  pre ms ==>
  m.weak ms ls ms' ==>
  post ms'
End

Theorem abstract_jgmt_imp_partial_triple:
 !m l ls pre post.
 weak_model m ==>
 abstract_jgmt m l ls pre post ==>
 abstract_partial_jgmt m l ls pre post
Proof
FULL_SIMP_TAC std_ss [abstract_jgmt_def, abstract_partial_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
metis_tac [weak_unique_thm]
QED

Theorem weak_partial_case_rule_thm:
 !m l ls pre post C1.
 abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
 abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
 abstract_partial_jgmt m l ls pre post
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
metis_tac []
QED

Theorem weak_partial_weakening_rule_thm:
 !m. 
 !l ls pre1 pre2 post1 post2.
 weak_model m ==>
 (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
 (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
 abstract_partial_jgmt m l ls pre1 post1 ==>
 abstract_partial_jgmt m l ls pre2 post2
Proof
SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_pc_in_thm]
QED

Theorem weak_partial_subset_rule_thm:
 !m. !l ls1 ls2 pre post.
 weak_model m ==>
 (!ms. post ms ==> (~(m.pc ms IN ls2))) ==>
 abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
 abstract_partial_jgmt m l ls1 pre post
Proof
rpt strip_tac >>
rfs [abstract_partial_jgmt_def] >>
rpt strip_tac >>
QSPECL_ASSUM ``!ms ms'. _`` [`ms`, `ms'`] >>
rfs [] >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
 fs []
) >>
subgoal `?n. FUNPOW_OPT m.trs n ms = SOME ms'` >- (
 metis_tac [weak_model_def]
) >>
IMP_RES_TAC weak_intermediate_labels >>
QSPECL_X_ASSUM ``!ms ms'. _`` [`ms`, `ms''`] >>
rfs [] >>
metis_tac []
QED


Theorem weak_partial_conj_rule_thm:
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  abstract_partial_jgmt m l ls pre post1 ==>
  abstract_partial_jgmt m l ls pre post2 ==>
  abstract_partial_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_unique_thm]
QED

(* Note: exactly abstract_jgmt_imp_partial_triple *)
Theorem total_to_partial:
 !m l ls pre post.
 weak_model m ==>
 abstract_jgmt m l ls pre post ==>
 abstract_partial_jgmt m l ls pre post
Proof
fs [abstract_jgmt_imp_partial_triple]
QED

Theorem weak_partial_seq_rule_thm:
 !m l ls1 ls2 pre post.
 weak_model m ==>
 abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
 (!l1. (l1 IN ls1) ==>
 (abstract_partial_jgmt m l1 ls2 post post)) ==>
 abstract_partial_jgmt m l ls2 pre post
Proof
rpt strip_tac >>
SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
subgoal `?ms'. m.weak ms (ls1 UNION ls2) ms'` >- (
 (* There is at least ms', possibly another state if ls1 is encountered before *)
 cheat
) >>
Cases_on `m.pc ms'' IN ls2` >- (
 (* If ls2 was reached without encountering ls1, we win immediately *)
  cheat
) >>
subgoal `m.pc ms'' IN ls1` >- (
 (* Set theory *)
  cheat
) >>
subgoal `?l1. m.pc ms'' = l1` >- (
 (* Technically requires ls1 non-empty, but if that is the case, we also win immediately *)
  cheat
) >>
subgoal `abstract_jgmt m l (ls1 UNION ls2) (\s. s = ms /\ pre s) (\s. (m.pc s IN ls1 ==> s = ms'') /\ (m.pc s IN ls2 ==> post s))` >- (
 fs [abstract_jgmt_def, abstract_partial_jgmt_def] >>
 qexists_tac ‘ms''’ >>
 fs []
) >>
subgoal `!l1'. (l1' IN ls1) ==> (abstract_jgmt m l1' ls2 (\s. (m.pc s IN ls1 ==> s = ms'') /\ (m.pc s IN ls2 ==> post s)) (\s. (m.pc s IN ls1 ==> s = ms'') /\ (m.pc s IN ls2 ==> post s)))` >- (
 rpt strip_tac >>
 fs [abstract_jgmt_def, abstract_partial_jgmt_def] >>
 rpt strip_tac >>
 res_tac >>
 subgoal `s' = ms''` >- (
  (* Both reached by m.weak ms (ls1 UNION ls2) *)
  metis_tac [weak_unique_thm]
 ) >>
 fs [] >>
 subgoal `m.weak ms'' ls2 ms'` >- (
  (* Since ms'' is a ls1-point encountered between ms and ls2 *)
   cheat
 ) >>
 qexists_tac ‘ms'’ >>
 fs [] >>
 (* OK: ms'3' is not in ls1 (weak_pc_in_thm) *)
 cheat
) >>
imp_res_tac abstract_seq_rule_thm >>
gs [abstract_jgmt_def] >>
subgoal `s' = ms'` >- (
 (* Both reached by m.weak ms ls2 *)
  metis_tac [weak_unique_thm]
) >>
subgoal `m.pc ms' IN ls2` >- (
 (* Reached by m.weak ms ls2 *)
  metis_tac [weak_pc_in_thm]
) >>
metis_tac []


(* OLD, working proof: *)
(*
rpt strip_tac >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!ms ms'.
		 (m.pc ms = l) ==>
		 pre ms ==>
		 m.weak ms (ls1 UNION ls2) ms' ==>
		 post ms'`` [`ms`] >>
rfs [] >>
subgoal `(m.pc ms') IN ls2` >- (
  metis_tac [weak_pc_in_thm]
) >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
  metis_tac []
) >>
subgoal `?ms''. m.pc ms'' IN ls1 /\ m.weak ms (ls2 UNION ls1) ms''` >- (
  metis_tac [weak_intermediate_labels, pred_setTheory.UNION_COMM]
) >>
QSPECL_X_ASSUM  ``!l1. l1 IN ls1 ==> _`` [`m.pc ms''`] >>
rfs [] >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms''`, `ms'`] >>
rfs [] >>
subgoal `post ms''` >- (
  metis_tac [pred_setTheory.UNION_COMM]
) >>
metis_tac [pred_setTheory.UNION_COMM, weak_intermediate_labels2]
*)
QED

Definition weak_partial_loop_contract_def:
  weak_partial_loop_contract m l le invariant C1 =
    (l NOTIN le /\
     abstract_partial_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms)
       (\ms. m.pc ms = l /\ invariant ms))
End

Theorem weak_superset_thm:
 !m.
 weak_model m ==>
 !ms ms' ls1 ls2.
 m.weak ms ls1 ms' ==>
 ?ms''. m.weak ms (ls1 UNION ls2) ms''
Proof
cheat
QED

Definition ominus_def:
 (ominus NONE _ = NONE) /\
 (ominus _ NONE = NONE) /\
 (ominus (SOME (n:num)) (SOME n') = SOME (n - n'))
End

Definition weak_exec_def:
 (weak_exec m ls ms =
  let
   MS' = m.weak ms ls
  in
   if MS' = {}
   then NONE
   else SOME (CHOICE MS'))
End

Definition weak_exec_n_def:
 (weak_exec_n m ms ls n = FUNPOW_OPT (weak_exec m ls) n ms)
End

(* TODO: Can prove equivalence here? *)
Theorem weak_exec_exists:
 !m.
 weak_model m ==>
 !ms ls ms'. 
 m.weak ms ls ms' ==>
 weak_exec m ls ms = SOME ms'
Proof
rpt strip_tac >>
fs [weak_exec_def] >>
subgoal `m.weak ms ls = {ms'}` >- (
 fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING, pred_setTheory.IN_APP] >>
 metis_tac [weak_unique_thm]
) >>
fs []
QED

(* TODO: Strengthen conclusion to state either ms'' is ms', or pc is in ls2? *)
Theorem weak_exec_exists_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'. 
 m.weak ms ls1 ms' ==>
 ?ms''. weak_exec m (ls1 UNION ls2) ms = SOME ms''
Proof
rpt strip_tac >>
fs [weak_exec_def] >>
(* OK: Either ms' is the result, or some other state with pc in ls2 was encountered before that *)
cheat
QED

Theorem weak_exec_n_exists_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'. 
 m.weak ms ls1 ms' ==>
 ?n. (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n
Proof
rpt strip_tac >>
(* OK: weak_exec_n is repeated applications of weak_exec. For every such application,
 * either ms' was encountered, or ls2, in which case some further number of steps
 * will encounter ms'. *)
cheat
QED

Theorem weak_exec_least_nonzero:
 !m.
 weak_model m ==>
 !ms ls ms' n_l.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 ms <> ms' ==>
 n_l > 0
Proof
rpt strip_tac >>
Cases_on `weak_exec_n m ms ls 0 = SOME ms'` >- (
 fs [weak_exec_n_def, FUNPOW_OPT_def]
) >>
(* TODO: Should be trivial: P 0 = F ==> (OLEAST n. P n) = SOME n_l ==> n_l > 0 *)
cheat
QED

Theorem weak_exec_sing_least_less:
 !m.
 weak_model m ==>
 !ms ls ms' n_l.
 SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms') ==>
 ?n_l'. (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l' /\ n_l' < n_l
Proof
rpt strip_tac >>
(* OK: If ms' is uniquely encountered before n_l loop iterations, then
 * there must be a least number of loop iterations such that ms' is
 * encountered, and this number is less than n_l *)
cheat
QED

Theorem weak_inter_exec:
 !m.
 weak_model m ==>
 !ms le l n_l ms' s'. 
 m.weak ms le ms' ==>
 (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms') = SOME n_l ==>
 SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME s') ==>
 m.weak s' le ms'
Proof
rpt strip_tac >>
(* OK: s' is a uniquely encountered (before n_l loop iterations) state,
 * where n_l is the least amount of applications of weak_exec to ({l} UNION le)
 * needed to exit the loop,
 * therefore weak transition can continue from s' to the loop exit *)
cheat
QED

(* TODO: Technically, this doesn't need OLEAST for the encounter of ms' *)
Theorem weak_exec_incr:
 !m.
 weak_model m ==>
 !ms ls ms' n_l ms''.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 m.weak ms' ls ms'' ==>
 weak_exec_n m ms ls (SUC n_l) = SOME ms''
Proof
rpt strip_tac >>
(* OK: ms'' reached by taking an additional weak transition from ms',
 * itself reached in n_l weak transitions, can also be reached by taking
 * n_l + 1 weak transitions *)
cheat
QED

(* TODO: Technically, this doesn't need OLEAST for the encounter of ms' *)
Theorem weak_exec_incr_least:
 !m.
 weak_model m ==>
 !ms ls ms' n_l n_l' ms''.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l' ==>
 m.weak ms' ls ms'' ==>
 SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms'') ==>
 n_l' < n_l ==>
 (OLEAST n. weak_exec_n m ms ls n = SOME ms'') = SOME (SUC n_l')
Proof
rpt strip_tac >>
(* OK: If ms' was first encountered at n_l' weak iterations to ls, and
 * if one additional weak transition to ls goes to ms'', then if
 * ms'' is uniquely encountered before n_l weak transitions to ls and n_l
 * is greater than n_l', then SUC n_l' must be the least number of weak transitions
 * needed to reach ms'' *)
cheat
QED

(* TODO: m.weak ms ls2 ms' redundant? *)
Theorem weak_exec_uniqueness:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' n_l. 
 m.weak ms ls2 ms' ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n_l ==>
 !n_l' ms''. n_l' < n_l ==>
 weak_exec_n m ms (ls1 UNION ls2) n_l' = SOME ms'' ==>
 SING (\n. n < n_l /\ weak_exec_n m ms (ls1 UNION ls2) n = SOME ms'')
Proof
rpt strip_tac >>
(* OK: ms'' is a state encountered before n_l loop iterations,
 * where n_l is the least amount of applications of weak_exec to ({l} UNION le)
 * needed to exit the loop,
 * therefore ms'' must have been uniquely encountered before n_l loop iterations,
 * or there must have been a loop before ms' could ever be reached *)
cheat
QED

(* Uses the fact that exit labels are disjoint from loop point to know that
 * we have not yet exited the loop after another weak transition, i.e. the
 * number of loops is still less than n_l *)
Theorem weak_exec_less_incr_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms'' ms''' n_l n_l'.
 DISJOINT ls1 ls2 ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n_l ==>
 m.pc ms' IN ls2 ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms'') = SOME n_l' ==>
 n_l' < n_l ==>
 m.weak ms'' (ls1 UNION ls2) ms''' ==>
 m.pc ms''' NOTIN ls2 ==>
 SUC n_l' < n_l
Proof
cheat
QED

(*
Theorem weak_exec_less:
 !m.
 weak_model m ==>
 !ms ls ms' n_l n_l'.
 SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms') ==>
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l' ==>
 n_l' < n_l
Proof
cheat
QED
*)

(*
Theorem weak_exec_comp1:
 !m.
 weak_model m ==>
 !ms ls ms' n n' ms''.
 weak_exec_n m ms ls n = SOME ms' ==>
 weak_exec_n m ms ls n' = SOME ms'' ==>
 n < n' ==>
 weak_exec_n m ms ls (n - n') = SOME ms''
Proof
cheat
QED
*)


(* Invariant: *)
(* TODO: Is SING useful enough or do we need LEAST? *)
val invariant = ``\s. (SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME s)) /\ invariant s``;


(* Variant: *)
(* TODO: Make different solution so that THE can be removed... *)
val variant = ``\s. THE (ominus (SOME n_l) ($OLEAST (\n. weak_exec_n m ms ({l} UNION le) n = SOME s)))``;

Theorem weak_partial_loop_rule_thm:
 !m.
 weak_model m ==>
 !l le invariant C1 var post.
 weak_partial_loop_contract m l le invariant C1 ==>
 abstract_partial_jgmt m l le (\ms. invariant ms /\ ~(C1 ms)) post ==>
 abstract_partial_jgmt m l le invariant post
Proof
rpt strip_tac >>
simp [abstract_partial_jgmt_def] >>
rpt strip_tac >>
fs [weak_partial_loop_contract_def] >>
(* 0. Establish n_l *)
subgoal `?n_l. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms') = SOME n_l` >- (
 ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
 irule weak_exec_n_exists_superset >>
 fs []
) >>

(* 1. Prove loop exit contract *)
subgoal `abstract_jgmt m l le (\s'. (^invariant) s' /\ ~(C1 s')) post` >- (
 fs [abstract_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s' <> ms'` >- (
  (* Since pc of s' is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
 ) >>
 subgoal `m.weak s' le ms'` >- (
  metis_tac [weak_inter_exec]
 ) >>
 fs [abstract_partial_jgmt_def] >>
 QSPECL_X_ASSUM ``!ms ms'. m.pc ms = l ==> invariant ms /\ ~C1 ms ==> m.weak ms le ms' ==> post ms'`` [`s'`, `ms'`] >>
 gs [] >>
 qexists_tac `ms'` >>
 metis_tac []
) >>

(* 2. Prove loop iteration contract *)
subgoal `abstract_loop_jgmt m l le (^invariant) C1 (^variant)` >- (
 fs [abstract_loop_jgmt_def, abstract_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s <> ms'` >- (
  (* Since pc of s is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
 ) >>
 (* n_l': the number of encounters of l up to s *)
 subgoal `?n_l'. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME s) = SOME n_l' /\ n_l' < n_l` >- (
  metis_tac [weak_exec_sing_least_less]
 ) >>
 (* ms''': next loop point *)
 subgoal `?ms'''. m.weak s ({l} UNION le) ms'''` >- (
  ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
  irule weak_superset_thm >>
  fs [] >>
  qexists_tac `ms'` >>
  metis_tac [weak_inter_exec]
 ) >>
 subgoal `m.pc ms''' = l` >- (
  fs [abstract_partial_jgmt_def] >>
  metis_tac []
 ) >>
 qexists_tac `ms'''` >>
 subgoal `SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME ms'3')` >- (
  (* Invariant is kept *)
  (* By uniqueness theorem (stating no duplicate states before ms' is reached) *)
  irule weak_exec_uniqueness >>
  fs [] >>
  conj_tac >| [
   qexists_tac `SUC n_l'` >>
   conj_tac >| [
    (* Since ms''' <> ms' *)
    irule weak_exec_less_incr_superset >>
    fs [] >>
    qexistsl_tac [`{l}`, `le`, `m`, `ms`, `ms'`, `s`, `ms'''`] >>
    fs [] >>
    metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm],

    metis_tac [weak_exec_incr]
   ],

   metis_tac []
  ]
 ) >>
 fs [] >>
 rpt strip_tac >| [
  (* By the contract for the looping case *)
  fs [abstract_partial_jgmt_def] >>
  metis_tac [],

  (* By arithmetic *)
  subgoal `(OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms'3') = SOME (SUC n_l')` >- (
   metis_tac [weak_exec_incr_least]
  ) >>
  fs [ominus_def]
 ]
) >>

imp_res_tac abstract_loop_rule_thm >>
fs [abstract_jgmt_def] >>
(* TODO: Should be provable using trs_to_ls m ({l} UNION le) ms n (SUC n_l) = SOME ms' *)
QSPECL_X_ASSUM  ``!s. m.pc s = l ==> _`` [`ms`] >>
subgoal `SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME ms)` >- (
 subgoal `weak_exec_n m ms ({l} UNION le) 0 = SOME ms` >- (
  fs [weak_exec_n_def, FUNPOW_OPT_def]
 ) >>
 subgoal `n_l > 0` >- (
  subgoal `ms <> ms'` >- (
   (* Since pc of ms is l, m.weak ms le ms' and l NOTIN le *)
   metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
  ) >>
  metis_tac [weak_exec_least_nonzero]
 ) >>
 (* By uniqueness theorem (stating no duplicate states before ms' is reached) *)
 irule weak_exec_uniqueness >>
 fs [] >>
 conj_tac >| [
  qexists_tac `0` >>
  fs [],

  metis_tac []
 ]
) >>
gs [] >>
metis_tac [weak_unique_thm]
QED

val _ = export_theory();
