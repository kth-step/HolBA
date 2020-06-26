open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logic_auxTheory;

val _ = new_theory "abstract_hoare_logic";

(* Judgment of the total-correctness logic *)
val abstract_jgmt_def = Define `
  abstract_jgmt m (l:'a) (ls:'a->bool) pre post =
  !ms .
   ((m.pc ms) = l) ==> (pre ms) ==>
   ?ms'. ((m.weak ms ls ms') /\
    (post ms'))
`;

(* TODO: Can this be rephrased better?
 * Antecedents guarantee swapping transition system of ANY contract. *)
val abstract_weak_model_comp_rule_thm = store_thm("abstract_weak_model_comp_rule_thm",
  ``!m n l ls pre post.
    weak_model m ==>
    weak_model n ==>
    (!ms ls ms'. m.weak ms ls ms' ==> n.weak ms ls ms') ==>
    (!ms l. (n.pc ms = l)  ==> (m.pc ms = l)) ==>
    abstract_jgmt m l ls pre post ==>
    abstract_jgmt n l ls pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!ms ls ms'. _`` [`ms`, `ls`, `ms'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `ms'` >>
FULL_SIMP_TAC std_ss []
);


val abstract_case_rule_thm = prove(``
!m l ls pre post C1.
  abstract_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  abstract_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  abstract_jgmt m l ls pre post
``,

rpt strip_tac >>
fs [abstract_jgmt_def] >>
metis_tac []
);

val abstract_conseq_rule_thm =
  store_thm("abstract_conseq_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    abstract_jgmt m l ls pre1 post1 ==>
    abstract_jgmt m l ls pre2 post2
  ``,

rpt strip_tac >>
fs [abstract_jgmt_def] >>
metis_tac [weak_pc_in_thm]
);



val abstract_subset_rule_thm =
 store_thm("abstract_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. ((post ms) ==> (~((m.pc ms) IN ls2)))) ==>
    abstract_jgmt m l (ls1 UNION ls2) pre post ==>
    abstract_jgmt m l ls1 pre post``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [abstract_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
METIS_TAC [weak_union_pc_not_in_thm]
);


val abstract_seq_rule_thm = store_thm("abstract_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    abstract_jgmt m l (ls1 UNION ls2) pre post ==>
    (!l1.
     l1 IN ls1 ==>
     abstract_jgmt m l1 ls2 post post
    ) ==>
    abstract_jgmt m l ls2 pre post``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [abstract_jgmt_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``abstract_jgmt m l (ls1 UNION ls2) pre post``
              (fn thm => ASSUME_TAC (SIMP_RULE std_ss [abstract_jgmt_def] thm)) >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `m.pc ms' IN ls2` >- (
  METIS_TAC [weak_union2_thm]
) >>
subgoal `m.pc ms' IN ls1` >- (
  METIS_TAC [weak_union_thm, weak_pc_in_thm]
) >>
QSPECL_X_ASSUM  ``!l1. _`` [`m.pc ms'`] >>
REV_FULL_SIMP_TAC std_ss [abstract_jgmt_def] >>
QSPECL_X_ASSUM  ``!m. _`` [`ms'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
METIS_TAC []
);


val abstract_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  abstract_jgmt m l ls pre post1 ==>
  abstract_jgmt m l ls pre post2 ==>
  abstract_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_jgmt_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_unique_thm]
);

(*
val weak_loop_step_def = Define `
  weak_loop_step m ms var l le invariant C1 =
    let x:num = var ms in
      (\ms'. m.weak ms ({l} UNION le) ms' /\
             (invariant ms /\ C1 ms) /\
             ((m.pc ms' = l) /\ invariant ms' /\ (var ms' < x) /\ (var ms' >= 0))
      )
`;
*)

(* TODO: Address minimum? (var ms' >= 0)
 *       Should this have assumption "WF wf_rel"?*)

val weak_loop_step_def = Define `
  weak_loop_step m ms wf_rel var l le invariant C1 =
    let x = var ms in
      (\ms'. (*(WF wf_rel) ==> *) (WF wf_rel) /\
             m.weak ms ({l} UNION le) ms' /\
             (invariant ms /\ C1 ms) /\
             ((m.pc ms' = l) /\ invariant ms' /\ (wf_rel (var ms') x))
      )
`;
(*
val loop_fun_defn =
  Hol_defn "loop_fun" `
    loop_fun m ms wf_rel var l le invariant C1  =
      let MS' = weak_loop_step m ms wf_rel var l le invariant C1 in
        if MS' = {}
        then ms
	else let ms' = (CHOICE MS') in
	       (loop_fun m ms' wf_rel var l le invariant C1)
`;
*)
(* For debugging:
Defn.tgoal loop_fun_defn
*)
(*
``?R'.
       WF R' /\
       !C1 invariant le l wf_rel var ms m MS' ms'.
           (MS' = weak_loop_step m ms wf_rel var l le invariant C1) /\
           MS' <> {} /\ (ms' = CHOICE MS') ==>
           R' (m,ms',wf_rel,var,l,le,invariant,C1)
             (m,ms,wf_rel,var,l,le,invariant,C1)``

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_loop_step_def] >>
Q.EXISTS_TAC `\(m, ms,wf_rel,var,l,le,invariant,C1) (m, ms',wf_rel,var,l,le,invariant,C1). wf_rel  (var ms) (var ms')` >>
REPEAT STRIP_TAC >| [
  (* This we need to have as assumption... *)
Q.EXISTS_TAC `\(m, ms,wf_rel',var,l,le,invariant,C1) (m, ms',wf_rel',var,l,le,invariant,C1). wf_rel (var ms) (var ms')` >>
  cheat,

  (* From assumption to be added... *)
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
  FULL_SIMP_TAC std_ss [] >>
  Q.ABBREV_TAC `MS' =  (\ms'.
	       WF wf_rel /\ m.weak ms ({l} UNION le) ms' /\ (invariant ms /\ C1 ms) /\
	       ((m.pc ms') = l) /\ invariant ms' /\ wf_rel (var ms') (var ms))` >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `MS'`, pred_setTheory.IN_ABS]
]
*)
(* TODO: Look at the resulting loop_fun_ind, see if you can prove it separately...*)
val loop_fun_ind = prove(
``!P.
  (!m ms wf_rel var l le invariant C1.
       (!MS' ms'.
	    (MS' = weak_loop_step m ms wf_rel var l le invariant C1) /\
	    MS' <> {} /\ (ms' = CHOICE MS') ==>
	    P m ms' wf_rel var l le invariant C1) ==>
       P m ms wf_rel var l le invariant C1) ==>
  !v v1 v2 v3 v4 v5 v6 v7. P v v1 v2 v3 v4 v5 v6 v7``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_loop_step_def] >>
QSPECL_X_ASSUM ``!m. _`` [`v`, `v1`, `v2`, `v3`, `v4`, `v5`, `v6`, `v7`] >>
Cases_on `WF v2` >>
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>

  Q.ABBREV_TAC `MS' =  (λms'.
          WF v2 ∧ v.weak v1 ({v4} ∪ v5) ms' ∧ (v6 v1 ∧ v7 v1) ∧
          (v.pc ms' = v4) ∧ v6 ms' ∧ v2 (v3 ms') (v3 v1))` >>
 ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  subgoal `MS' <> {}` >- (
    cheat
  ) >>
FULL_SIMP_TAC std_ss [] >>
cheat
);



(*
val (loop_fun_eqns, loop_fun_ind) =
  Defn.tprove(loop_fun_defn,

FULL_SIMP_TAC std_ss [weak_loop_step_def] >>
Q.EXISTS_TAC `\(m, ms,wf_rel,var,l,le,invariant,C1) (m, ms',wf_rel,var,l,le,invariant,C1). wf_rel (var ms) (var ms')` >>
REPEAT STRIP_TAC >| [
  (* This we need to have as assumption... *)
  cheat,

  (* From assumption to be added... *)
  subgoal `WF wf_rel` >- (
    cheat
  ) >>
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
  FULL_SIMP_TAC std_ss [] >>
  Q.ABBREV_TAC `MS' =  (\ms'.
	       m.weak ms ({l} UNION le) ms' /\ (invariant ms /\ C1 ms) /\
	       ((m.pc ms') = l) /\ invariant ms' /\ wf_rel (var ms') (var ms))` >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `MS'`, pred_setTheory.IN_ABS]
]
);
*)

val abstract_loop_jgmt_def = Define `
  abstract_loop_jgmt m l le invariant C1 wf_rel var =
    l NOTIN le /\ WF wf_rel /\
    (!x. (abstract_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms /\ (var ms = x))
         (\ms. (m.pc ms = l) /\ invariant ms /\ (wf_rel (var ms) x))))
`;

(* Note that due to loop_fun_ind relating states ms and ms' at loop points,
 * ms needs to be exposed also here. Either this can be explicitly specified
 * in the precondition of the conclusion, or the definition can be unfolded, like here *)
val loop_fun_ind_spec =
  Q.SPEC `\m ms wf_rel var l le invariant C1.
	   weak_model m ==>
           WF wf_rel ==>
	   abstract_loop_jgmt m l le invariant C1 wf_rel var ==>
	   abstract_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
	   (invariant ms /\ (m.pc ms = l) /\ C1 ms) ==>
	   (?ms'. m.weak ms le ms' /\ post ms')` loop_fun_ind;


(*
   ``!m ms wf_rel var l le invariant C1.
         (!MS' ms'.
              (MS' = weak_loop_step m ms wf_rel var l le invariant C1) /\
              MS' <> {} /\ (ms' = CHOICE MS') ==>
              (\m ms wf_rel var l le invariant C1.
                   weak_model m ==>
                   WF wf_rel ==>
                   abstract_loop_jgmt m l le invariant C1 wf_rel var ==>
                   weak_triple m l le (\ms. invariant ms /\ ~C1 ms) post ==>
                   invariant ms /\ (m.pc ms = l) /\ C1 ms ==>
                   ?ms'. m.weak ms le ms' /\ post ms') m ms' wf_rel var l le
                invariant C1) ==>
         (\m ms wf_rel var l le invariant C1.
              weak_model m ==>
              WF wf_rel ==>
              abstract_loop_jgmt m l le invariant C1 wf_rel var ==>
              weak_triple m l le (\ms. invariant ms /\ ~C1 ms) post ==>
              invariant ms /\ (m.pc ms = l) /\ C1 ms ==>
              ?ms'. m.weak ms le ms' /\ post ms') m ms wf_rel var l le
           invariant C1``
*)

val inductive_invariant_goal = fst $ dest_imp $ concl loop_fun_ind_spec;

(* Below is still TODO... *)
val inductive_invariant = prove(``
^inductive_invariant_goal
``,

(* New proof without wf_rel:
rpt strip_tac >>
fs [] >>
rpt strip_tac >>
Cases_on `~C1 ms` >- (
  fs [abstract_jgmt_def]
) >>
(* We first prove that one iteration works (first antecedent of induction hypothesis):
 * OK since C1 holds in ms, then use loop judgment to obtain
 * witness *)
subgoal `loop_step m ms var l le invariant C1 <> {}` >- (
  simp [loop_step_def, LET_DEF] >>
  fs [abstract_loop_jgmt_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`(var ms):num`] >>
  fs [abstract_jgmt_def] >>
  QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
  rfs [] >>
  fs [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  qexists_tac `ms'':'a` >>
  fs [pred_setTheory.SPECIFICATION]
) >>
(* There first four antecedents of the induction hypothesis are now in place *)
fs [] >>
(* Let ms' be the state at the next loop iteration *)
Q.ABBREV_TAC `MS' = loop_step m ms var l le invariant C1` >>
Q.ABBREV_TAC `ms' = CHOICE MS'` >>
subgoal `loop_step m ms var l le invariant C1 ms'` >- (
  fs [Abbr `ms'`] >>
  ONCE_REWRITE_TAC [GSYM pred_setTheory.SPECIFICATION] >>
  metis_tac [pred_setTheory.CHOICE_DEF]
) >>
(* We then prove that the invariant is preserved and loop
 * point is l
 * (follows from ms' being the result of a loop_step) *)
subgoal `invariant ms' /\ (m.pc ms') = l` >- (
  fs [loop_step_def, LET_DEF]
) >>
fs [] >>
(* For both cases, weak_comp_thm is used to connect ms to ms'' via ms'. *)
fs [loop_step_def, LET_DEF] >>
`m.weak ms le ms''` suffices_by (
  metis_tac []
) >>
irule weak_comp_thm >>
fs [] >>
qexistsl_tac [`{l}`, `ms'`] >>
Q.SUBGOAL_THEN `l NOTIN le` (fn thm => fs [thm]) >- (
  fs [abstract_loop_jgmt_def, pred_setTheory.IN_SING]
)
*)
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
(* We first prove that one iteration works *)
subgoal `(weak_loop_step m ms wf_rel var l le invariant C1) <> {}`  >- (
  SIMP_TAC std_ss [weak_loop_step_def, LET_DEF] >>
  FULL_SIMP_TAC std_ss [abstract_loop_jgmt_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`var ms`] >>
  FULL_SIMP_TAC std_ss [abstract_jgmt_def] >>
  QSPECL_X_ASSUM ``!ms'. _`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  EXISTS_TAC ``ms'':'a`` >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
FULL_SIMP_TAC std_ss [] >>

Q.ABBREV_TAC `MS' = (weak_loop_step m ms wf_rel var l le invariant C1)` >>
Q.ABBREV_TAC `ms' = CHOICE MS'` >>

(* We prove that the invariant is preserved *)
SUBGOAL_THEN ``(weak_loop_step m ms wf_rel var l le invariant C1) ms'`` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [Abbr `ms'`] >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF) >>
  REV_FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
Q.SUBGOAL_THEN `invariant ms'` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(m.pc ms') = l` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>

(* If we exit the loop *)
Cases_on `~ (C1 ms')` >- (
  (FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]) >>
  (FULL_SIMP_TAC std_ss [abstract_jgmt_def]) >>
  QSPECL_X_ASSUM  ``!x. _`` [`ms'`] >>
  (REV_FULL_SIMP_TAC std_ss []) >>
  ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!x. _`` [`ms`, `{l}`, `le`, `ms'`, `ms''`] >>
  REV_FULL_SIMP_TAC (std_ss) [SINGLETONS_UNION_thm] >>
  Q.SUBGOAL_THEN `l NOTIN le` (FULLSIMP_BY_THM std_ss) >- (
    FULL_SIMP_TAC std_ss [abstract_loop_jgmt_def, pred_setTheory.IN_SING]
  ) >>
  METIS_TAC []
) >> (
  FULL_SIMP_TAC std_ss []
) >> (
  FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]
) >>
ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!x. _`` [`ms`, `{l}`, `le`, `ms'`, `ms''`] >>
REV_FULL_SIMP_TAC (std_ss) [SINGLETONS_UNION_thm] >>
  Q.SUBGOAL_THEN `l NOTIN le` (FULLSIMP_BY_THM std_ss) >- (
    FULL_SIMP_TAC std_ss [abstract_loop_jgmt_def, pred_setTheory.IN_SING]
  ) >>
  METIS_TAC []
);

(* Now just some final touches to get the theorem in the exact shape we want *)
val abstract_loop_rule_tmp_thm = MP loop_fun_ind_spec inductive_invariant;

(* OLD:
val invariant_rule_tmp_thm = 
MP 
(Q.SPEC `(\m ms wf_rel var l le invariant C1.
weak_model m ==>
WF wf_rel ==>
abstract_loop_jgmt m l le invariant C1 wf_rel var ==>
abstract_jgmt m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
((invariant ms) /\ ((m.pc ms) = l) /\ (C1 ms)) ==>
 (?ms'. ((m.weak ms le ms') /\ (post ms'))))` loop_fun_ind) inductive_invariant_thm;
*)

val abstract_loop_rule_thm = store_thm("abstract_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 wf_rel var post.
    WF wf_rel ==>
    abstract_loop_jgmt m l le invariant C1 wf_rel var ==>
    abstract_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
    abstract_jgmt m l le invariant post``,


metis_tac [abstract_jgmt_def, abstract_loop_rule_tmp_thm]
(* OLD:
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [abstract_jgmt_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`m`, `ms`, `wf_rel`, `var`, `l`, `le`, `invariant`, `C1`] invariant_rule_tmp_thm) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `C1 ms` >- (
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ms'`>>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [abstract_jgmt_def] 
*)
);

val _ = export_theory();
