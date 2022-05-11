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


Theorem weak_partial_seq_rule_thm:
 !m l ls1 ls2 pre post.
 weak_model m ==>
 abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
 (!l1. (l1 IN ls1) ==>
 (abstract_partial_jgmt m l1 ls2 post post)) ==>
 abstract_partial_jgmt m l ls2 pre post
Proof
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
QED


Theorem weak_rel_steps_list_states_subgoal_2_lemma:
!m n ms ms' ms_list ls l.
 weak_model m ==>
 n > 0 ==>
 INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (PRE n,ms') ==>
 l NOTIN ls ==>
 FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
 FILTER (\ms. m.pc ms = l) ms_list = [] ==>
 INDEX_FIND 0 (\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) ms_list =
        SOME (PRE n,ms')
Proof
rpt strip_tac >>
Q.SUBGOAL_THEN `(\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) = (\ms''. (\ms'''. m.pc ms''' IN ls) ms'' \/ (\ms'''. m.pc ms''' IN {l}) ms'')` (fn thm => REWRITE_TAC [thm]) >- (
 fs [] >>
 metis_tac []
) >>
irule FUNPOW_OPT_LIST_FILTER_NULL >>
fs [] >>
metis_tac []
QED

Theorem weak_rel_steps_list_states_subgoal_3_lemma:
!m n ms ms' ms_list ls l.
 weak_model m ==>
 INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (PRE n,ms') ==>
 l NOTIN ls ==>
 FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
 LENGTH (FILTER (\ms. m.pc ms = l) ms_list) > 0 ==>
 ?n'.
   (n' > 0 /\
    ?ms_list'.
      FUNPOW_OPT_LIST m.trs n' ms = SOME (ms::ms_list') /\
      INDEX_FIND 0 (\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) ms_list' =
      SOME (PRE n',HD (FILTER (\ms. m.pc ms = l) ms_list))) /\
   (n > n' /\
    ?ms_list'.
      FUNPOW_OPT_LIST m.trs (n - n')
        (HD (FILTER (\ms. m.pc ms = l) ms_list)) =
      SOME (HD (FILTER (\ms. m.pc ms = l) ms_list)::ms_list') /\
      INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list' =
      SOME (PRE (n - n'),ms')) /\ n' < n /\ n' > 0
Proof
rpt strip_tac >>
Q.SUBGOAL_THEN `(\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) = (\ms''. (\ms'''. m.pc ms''' IN {l}) ms'' \/ (\ms'''. m.pc ms''' IN ls) ms'')` (fn thm => REWRITE_TAC [thm]) >- (
 fs [] >>
 metis_tac []
) >>
Q.SUBGOAL_THEN `(\ms''. m.pc ms'' = l) = (\ms'3'. m.pc ms'3' IN {l})` (fn thm => REWRITE_TAC [thm]) >- (
 fs [] >>
 metis_tac []
) >>
irule FUNPOW_OPT_LIST_FILTER_FIRST >>
fs [] >>
subgoal `ms' = LAST ms_list` >- (
 fs [INDEX_FIND_EQ_SOME_0] >>
 fs [FUNPOW_OPT_LIST_EQ_SOME] >>
 rw [] >>
 ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
 irule listTheory.LAST_EL >>
 (* TODO: Find nice lemma for this... *)
 Cases_on `ms_list` >> (
  fs []
 )
) >>
fs [INDEX_FIND_EQ_SOME_0] >>
metis_tac [IN_NOT_IN_NEQ_thm]
QED

Theorem weak_rel_steps_list_states_subgoal_4_lemma:
!m n ms ms' ms_list ls l.
 weak_model m ==>
 INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (PRE n,ms') ==>
 l NOTIN ls ==>
 FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
 LENGTH (FILTER (\ms. m.pc ms = l) ms_list) > 0 ==>
 ?n''.
   (?ms_list'.
      FUNPOW_OPT_LIST m.trs n''
        (EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1)
           (FILTER (\ms. m.pc ms = l) ms_list)) =
      SOME
        (EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1)
             (FILTER (\ms. m.pc ms = l) ms_list)::ms_list') /\
      INDEX_FIND 0 (\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) ms_list' =
      SOME (PRE n'',ms')) /\ n'' > 0
Proof
rpt strip_tac >>
subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
 fs []
) >>
Q.SUBGOAL_THEN `EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1)
                  (FILTER (\ms. m.pc ms = l) ms_list) = LAST ms_list'` (fn thm => REWRITE_TAC [thm]) >- (
 (* By listTheory.LAST_EL *)
 fs [] >>
 ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
 ONCE_REWRITE_TAC [GSYM arithmeticTheory.PRE_SUB1] >>
 irule listTheory.LAST_EL >>
 fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
) >>
Q.SUBGOAL_THEN `(\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) = (\ms''. (\ms'''. m.pc ms''' IN {l}) ms'' \/ (\ms'''. m.pc ms''' IN ls) ms'')` (fn thm => REWRITE_TAC [thm]) >- (
 fs [] >>
 metis_tac []
) >>
irule FUNPOW_OPT_LIST_FILTER_LAST >>
fs [] >>
qexists_tac `n` >>
qexists_tac `ms` >>
qexists_tac `ms_list` >>
fs []
QED

Theorem weak_rel_steps_list_states_subgoal_5_lemma:
!m n ms ms' ms_list ls l i.
 weak_model m ==>
 INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (PRE n,ms') ==>
 l NOTIN ls ==>
 FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
 i < LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1 ==>
 ?n' n''.
  (?ms_list'.
   FUNPOW_OPT_LIST m.trs n'
     (EL i (FILTER (\ms. m.pc ms = l) ms_list)) =
   SOME (EL i (FILTER (\ms. m.pc ms = l) ms_list)::ms_list') /\
   INDEX_FIND 0 (\ms''. m.pc ms'' = l \/ m.pc ms'' IN ls) ms_list' =
   SOME (PRE n',EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list))) /\
  (?ms_list'.
   FUNPOW_OPT_LIST m.trs n''
     (EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list)) =
   SOME (EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list)::ms_list') /\
   INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list' = SOME (PRE n'',ms')) /\
  n' < n /\ n' > 0 /\ n'' < n /\ n'' > 0
Proof
metis_tac [FUNPOW_OPT_LIST_FILTER_BETWEEN]
QED

(* This describes the necessary characteristics of the list ms_list, which consists of
 * all states where l is encountered between ms and ms'. *)
Theorem weak_rel_steps_list_states:
!m ms l ls ms' n.
 weak_model m ==>
 weak_rel_steps m ms ls ms' n ==>
 l NOTIN ls ==>
 ?ms_list.
  (!i. i < LENGTH ms_list ==> m.pc (EL i ms_list) = l) /\
  (LENGTH ms_list = 0 ==> weak_rel_steps m ms ({l} UNION ls) ms' n) /\
  (LENGTH ms_list > 0 ==>
   (?n'. weak_rel_steps m ms ({l} UNION ls) (HD ms_list) n' /\
         weak_rel_steps m (HD ms_list) ls ms' (n - n') /\ n' < n /\ n' > 0) /\
   (?n''. weak_rel_steps m (EL ((LENGTH ms_list) - 1) ms_list) ({l} UNION ls) ms' n'' /\ n'' > 0) /\
    !i. (i < ((LENGTH ms_list) - 1) ==> ?n' n''.
         weak_rel_steps m (EL i ms_list) ({l} UNION ls) (EL (i+1) ms_list) n' /\
         weak_rel_steps m (EL (i+1) ms_list) ls ms' n'' /\ n' < n /\ n' > 0 /\ n'' < n /\ n'' > 0))
Proof
rpt strip_tac >>
subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list)` >- (
 fs [weak_rel_steps_def] >>
 IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS >>
 QSPECL_X_ASSUM ``!n'. n' <= n ==> ?l. FUNPOW_OPT_LIST m.trs n' ms = SOME l`` [`n`] >>
 fs [] >>
 Cases_on `n` >- (
  fs [FUNPOW_OPT_LIST_def]
 ) >>
 subgoal `?ms''. m.trs ms = SOME ms''` >- (
  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  QSPECL_X_ASSUM ``!n''. n'' <= SUC n' ==> FUNPOW_OPT m.trs n'' ms = SOME (EL n'' l')`` [`1`] >>
  fs [FUNPOW_OPT_compute] >>
  Cases_on `m.trs ms` >> (
   fs []
  )
 ) >>
 subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n' ms'' = SOME ms_list` >- (
  metis_tac [FUNPOW_OPT_LIST_BACK_PRE]
 ) >>
 qexists_tac `ms_list` >>
 (* TODO: Should be OK...
  * (see also first subgoal in weak_rel_steps_smallest_exists, reuse this?) *)
 IMP_RES_TAC FUNPOW_OPT_LIST_BACK_INCR >>
 fs []
) >>
qexists_tac `FILTER (\ms. m.pc ms = l) ms_list` >>
rpt strip_tac >| [
 (* subgoal 1. OK: by FILTER_MEM *)
 subgoal `(\ms. m.pc ms = l) (EL i (FILTER (\ms. m.pc ms = l) ms_list))` >- (
  (* TODO: Silly, but it works... *)
  `(\ms. m.pc ms = l) (EL i (FILTER (\ms. m.pc ms = l) ms_list)) /\ MEM (EL i (FILTER (\ms. m.pc ms = l) ms_list)) ms_list` suffices_by (
   fs []
  ) >>
  irule FILTER_MEM >>
  qexists_tac `FILTER (\ms. m.pc ms = l) ms_list` >>
  metis_tac [listTheory.MEM_EL]
 ) >>
 fs [],

 (* subgoal 2. OK: If filtered list is empty, l can be inserted in ending label set
  * See FUNPOW_OPT_LIST_FILTER_NULL *)
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_to_FUNPOW_OPT_LIST thm]) >>
 metis_tac [weak_rel_steps_list_states_subgoal_2_lemma],

 (* subgoal 3. OK: First encounter of l is reached when filtered list is non-empty,
  * also weak transition can proceed from there directly to ending label set
  * See FUNPOW_OPT_LIST_FILTER_FIRST *)
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_to_FUNPOW_OPT_LIST thm]) >>
 metis_tac [weak_rel_steps_list_states_subgoal_3_lemma],

 (* subgoal 4. OK: Last element in filtered list can perform weak transition with ending
  * label set ({l} UNION ls) and reach ms' *)
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_to_FUNPOW_OPT_LIST thm]) >>
 metis_tac [weak_rel_steps_list_states_subgoal_4_lemma],
(* OLD:
 subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
  fs []
 ) >>
 subgoal `MEM (EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list)) ms_list` >- (
  subgoal `MEM (EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [listTheory.MEM_EL] >>
   qexists_tac `PRE (LENGTH ms_list')` >>
   fs []
  ) >>
  metis_tac [FILTER_MEM]
 ) >>
 (* Note : this introduces n'3', the number of transitions to last encounter of l. *)
 subgoal `?n'''. FUNPOW_OPT m.trs n''' ms = SOME (EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1) (FILTER (\ms. m.pc ms = l) ms_list)) /\ n''' < n /\ n''' > 0` >- (
  fs [listTheory.MEM_EL] >>
  qexists_tac `SUC n'` >>
  rpt CONJ_TAC >| [
   fs [FUNPOW_OPT_LIST_EQ_SOME, arithmeticTheory.PRE_SUB1] >>
   rw [],
   
   (* TODO: Last element of ms_list' not being in l contradiction *)
   metis_tac [weak_rel_steps_FILTER_NOTIN_end],

   fs []
  ]
 ) >>
 IMP_RES_TAC weak_rel_steps_intermediate_start >>
 qexists_tac `n - n'3'` >>
 fs [] >>
 ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
 irule weak_rel_steps_superset_after >>
 rpt strip_tac >> (
  fs []
 ) >| [
  (* Find appropriate index in ms_list and use it, also lemma that indices after FILTER LAST do
   * not have label l *)
  qexists_tac `EL (PRE (n' + n'3')) ms_list` >>
  CONJ_TAC >| [
   (* TODO: Lemma for this situation *)
   irule FUNPOW_OPT_split >>
   qexists_tac `n'3'` >>
   qexists_tac `ms` >>
   fs [] >>
   metis_tac [FUNPOW_OPT_todoname],

(*
   subgoal `n'3' < n` >- (
    fs []
   ) >>
*)
   subgoal `EL (PRE n'3') ms_list = LAST ms_list'` >- (
    subgoal `FUNPOW_OPT m.trs n'3' ms = SOME (EL (PRE n'3') ms_list)` >- (
     fs [FUNPOW_OPT_LIST_EQ_SOME] >>
     QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' (ms::ms_list))`` [`n'3'`] >>
     rfs [rich_listTheory.EL_CONS]
    ) >>
    subgoal `EL (PRE n'3') ms_list = EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1)
             (FILTER (\ms. m.pc ms = l) ms_list)` >- (
     fs []
    ) >>
    fs [] >>
    ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
    ONCE_REWRITE_TAC [GSYM arithmeticTheory.PRE_SUB1] >>
    irule listTheory.LAST_EL >>
    fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
   ) >>
   IMP_RES_TAC FILTER_AFTER >>
   QSPECL_X_ASSUM ``!i'. i' > PRE n'3' ==> ~(\ms. m.pc ms = l) (EL i' ms_list)`` [`(PRE (n' + n'3'))`] >>
   `PRE (n' + n'3') > PRE n'3'` suffices_by (
    fs []
   ) >>
   Cases_on `n'` >- (
    fs []
   ) >>
   Cases_on `n'3'` >> (
    fs []
   )
  ],

  metis_tac []
 ],
*)

 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_to_FUNPOW_OPT_LIST thm]) >>
 metis_tac [weak_rel_steps_list_states_subgoal_5_lemma]
 (* subgoal 5. Inductive case for weak transition with ending label set ({l} UNION ls)
  * between elements of the list (where the latter point goes to ms' with ending label set ls).
  * Should also be OK *)

(* OLD
 subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
  fs []
 ) >>
 subgoal `?i'. EL i' ms_list = EL i (FILTER (\ms. m.pc ms = l) ms_list) /\ i' < LENGTH ms_list` >- (
  subgoal `MEM (EL i (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [rich_listTheory.EL_MEM]
  ) >>
  fs [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  qexists_tac `n'` >>
  rw []
 ) >>
 subgoal `?i'. EL i' ms_list = EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list) /\ i' < LENGTH ms_list` >- (
  subgoal `MEM (EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [rich_listTheory.EL_MEM]
  ) >>
  fs [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  qexists_tac `n'` >>
  rw []
 ) >>
 subgoal `i' < i''` >- (
  irule FILTER_ORDER >>
  qexists_tac `(\ms. m.pc ms = l)` >>
  qexists_tac `i` >>
  qexists_tac `ms_list` >>
  fs [arithmeticTheory.ADD1]
 ) >>
 subgoal `n = LENGTH ms_list` >- (
  fs [FUNPOW_OPT_LIST_EQ_SOME]
 ) >>
 qexists_tac `SUC i'' - SUC i'` >>
 qexists_tac `n - (SUC i'')` >>
 fs [] >>
 rpt strip_tac >| [
  (* Weak transtion to ({l} UNION ls) between element i and element i+1 in ms_list' *)
  metis_tac [weak_rel_steps_FILTER_inter],

  (* Weak transtion to ls between element i+1 and LAST of ms_list' *)
  metis_tac [weak_rel_steps_FILTER_end],

  (* Phrased differently: "Why can't a member of ms_list' be the last element in ms_list?" *)
  (* TODO: Last element of ms_list' not being in l contradiction *)
  Cases_on `SUC i'' = LENGTH ms_list` >- (
   fs [weak_rel_steps_def] >>
   subgoal `m.pc (EL i'' ms_list) = l` >- (
    subgoal `MEM (EL i'' ms_list) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
     fs [listTheory.MEM_EL] >>
     qexists_tac `i + 1` >>
     fs []
    ) >>
    fs [listTheory.MEM_FILTER]
   ) >>

   subgoal `ms' = EL i'' ms_list` >- (
    fs [FUNPOW_OPT_LIST_EQ_SOME, listTheory.LAST_EL] >>
    metis_tac [listTheory.EL_restricted]
   ) >>
   metis_tac []
  ) >>
  fs []
 ]
*)
]
QED

Definition weak_partial_loop_contract_def:
  weak_partial_loop_contract m l le invariant C1 =
    (l NOTIN le /\
     abstract_partial_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms)
       (\ms. m.pc ms = l /\ invariant ms))
End

Theorem weak_partial_loop_rule_thm:
 !m.
 weak_model m ==>
 !l le invariant C1 var post.
 weak_partial_loop_contract m l le invariant C1 ==>
 abstract_partial_jgmt m l le (\ms. invariant ms /\ ~(C1 ms)) post ==>
 abstract_partial_jgmt m l le invariant post
Proof
rpt strip_tac >>
fs [abstract_partial_jgmt_def, weak_partial_loop_contract_def] >>
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
IMP_RES_TAC weak_rel_steps_list_states >>
(* QSPECL_X_ASSUM  ``!l. ?ms_list. _`` [`l`] >> *)
fs [] >>
Cases_on `ms_list = []` >- (
 fs [] >>
 QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms`, `ms'`] >>
 QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms`, `ms'`] >>
 rfs [] >>
 Cases_on `C1 ms` >| [
  metis_tac [weak_pc_in_thm, weak_rel_steps_imp],

  metis_tac []
 ]
) >>
subgoal `LENGTH ms_list > 0` >- (
 fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
) >>
fs [] >>
Cases_on `~C1 ms` >- (
 metis_tac []
) >>
fs [] >>
subgoal `m.pc ms' <> l` >- (
  metis_tac [weak_pc_in_thm, weak_rel_steps_imp]
) >>
subgoal `!i. i < LENGTH ms_list ==> 
             (invariant (EL i ms_list) \/ post ms') /\
             (C1 (EL i ms_list) \/ (~C1 (EL i ms_list) /\ post ms'))` >- (
 Induct_on `i` >- (
  fs [] >>
  QSPECL_X_ASSUM  ``!i. _`` [`0`] >>
  subgoal `invariant (EL 0 ms_list)` >- (
   fs [] >>
   metis_tac [weak_rel_steps_intermediate_labels3, pred_setTheory.IN_SING]
  ) >>
  fs [] >>
  Cases_on `C1 (HD ms_list)` >> (
   fs []
  ) >>
  PAT_X_ASSUM  ``!ms ms'. _`` (fn thm => irule thm) >>
  qexists_tac `HD ms_list` >>
  fs [] >>
  metis_tac []
 ) >>
 rpt strip_tac >> (
  fs []
 ) >| [
  QSPECL_X_ASSUM  ``!ms'' ms'3'.
          m.pc ms'' = l ==>
          invariant ms'' /\ C1 ms'' ==>
          (?n. weak_rel_steps m ms'' ({l} UNION le) ms'3' n) ==>
          m.pc ms'3' = l /\ invariant ms'3'`` [`EL i ms_list`, `EL (SUC i) ms_list`] >>
  QSPECL_X_ASSUM  ``!i. i < LENGTH ms_list ==> m.pc (EL i ms_list) = l`` [`i`] >>
  fs [] >>
  rfs [] >>
  QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
  rfs [] >>
  `?n. weak_rel_steps m (EL i ms_list) ({l} UNION le) (EL (SUC i) ms_list) n` suffices_by (
   fs []
  ) >>
  qexists_tac `n'3'` >>
  fs [arithmeticTheory.SUC_ONE_ADD],

  Cases_on `C1 (EL (SUC i) ms_list)` >> (
   fs []
  ) >>
  subgoal `invariant (EL (SUC i) ms_list)` >- (
   QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
   QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
   rfs [arithmeticTheory.SUC_ONE_ADD] >>
   metis_tac []
  ) >>
  PAT_X_ASSUM  ``!ms ms'. _`` (fn thm => irule thm) >>
  QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
  Cases_on `SUC i = LENGTH ms_list - 1` >- (
   (* SUC i is last in ms_list *)
   QSPECL_X_ASSUM  ``!i. _`` [`SUC i`] >>
   qexists_tac `EL (SUC i) ms_list` >>
   fs [] >>
   rfs [] >>
   PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_rel_steps_equiv thm)]) >>
   metis_tac [weak_union_thm, pred_setTheory.IN_SING, weak_rel_steps_equiv]
  ) >>
  subgoal `SUC i < LENGTH ms_list - 1` >- (
   fs []
  ) >>
  fs [] >>
  qexists_tac `EL (SUC i) ms_list` >>
  fs [arithmeticTheory.SUC_ONE_ADD] >>
  metis_tac []
 ]
) >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`EL (LENGTH ms_list − 1) ms_list`, `ms'`] >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`EL (LENGTH ms_list − 1) ms_list`, `ms'`] >>
subgoal `MEM (EL (LENGTH ms_list − 1) ms_list) ms_list` >- (
 subgoal `LENGTH ms_list − 1 < LENGTH ms_list` >- (
  fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
 ) >>
 metis_tac [rich_listTheory.EL_MEM]
) >>
rfs [] >>
Cases_on `C1 (EL (LENGTH ms_list − 1) ms_list)` >> (
 fs [] >>
 QSPECL_X_ASSUM  ``!i. _`` [`LENGTH ms_list − 1`] >>
 QSPECL_X_ASSUM  ``!i. _`` [`LENGTH ms_list − 1`] >>
 fs [] >>
 rfs [] >>
 fs []
)
QED

val _ = export_theory();
