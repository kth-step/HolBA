open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open transition_systemTheory;

val _ = new_theory "total_program_logic";

(* Judgment of the total-correctness logic *)
Definition t_jgmt_def:
 t_jgmt TS (l:'b) (ls:'b->bool) pre post =
  !s.
   TS.ctrl s = l ==>
   pre s ==>
   ?s'. TS.weak ls s s' /\ post s'
End


(* TODO: Can this be rephrased better?
 * Antecedents guarantee swapping transition system of ANY contract. *)
(* Rule for transferring contracts from embedded transition systems:
 * Here, TS' embedded in TS. *)
Theorem total_emb_rule_thm:
 !TS TS'.
  first_enc TS ==>
  first_enc TS' ==>
  (!ls s s'. TS.weak ls s s' ==> TS'.weak ls s s') ==>
  (!s l. (TS'.ctrl s = l)  ==> (TS.ctrl s = l)) ==>
  !l ls pre post.
   t_jgmt TS l ls pre post ==>
   t_jgmt TS' l ls pre post
Proof
rpt strip_tac >>
fs [t_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
rfs [] >>
fs [] >>
QSPECL_X_ASSUM ``!ls s s'. _`` [`ls`, `s`, `s'`] >>
rfs [] >>
Q.EXISTS_TAC `s'` >>
fs []
QED


(* Rule for combining contracts with a case split on the initial state *)
Theorem total_case_rule_thm:
 !m l ls pre post C1.
  t_jgmt m l ls (\ms. pre ms /\ C1 ms) post ==>
  t_jgmt m l ls (\ms. pre ms /\ ~(C1 ms)) post ==>
  t_jgmt m l ls pre post
Proof
rpt strip_tac >>
fs [t_jgmt_def] >>
metis_tac []
QED


(* Rule of consequence *)
Theorem total_conseq_rule_thm:
 !TS. 
  !l ls pre1 pre2 post1 post2.
  first_enc TS ==>
  (!s. TS.ctrl s = l ==> pre2 s ==> pre1 s) ==>
  (!s. TS.ctrl s IN ls ==> post1 s ==> post2 s) ==>
  t_jgmt TS l ls pre1 post1 ==>
  t_jgmt TS l ls pre2 post2
Proof
rpt strip_tac >>
fs [t_jgmt_def] >>
metis_tac [weak_ctrl_in]
QED

(* Rule allowing labels in the ending label list to
 * be removed, if postcondition implies they are not
 * encountered *)
Theorem total_subset_rule_thm:
 !TS.
  !l ls1 ls2 pre post.
   first_enc TS ==>
   (!s. post s ==> ~(TS.ctrl s IN ls2)) ==>
   t_jgmt TS l (ls1 UNION ls2) pre post ==>
   t_jgmt TS l ls1 pre post
Proof
rpt strip_tac >>
rfs [t_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
metis_tac [weak_union_ctrl_not_in]
QED

(* Rule for sequential composition *)
Theorem total_seq_rule_thm:
 !TS l ls1 ls2 pre post.
  first_enc TS ==>
  t_jgmt TS l (ls1 UNION ls2) pre post ==>
  (!l1.
   l1 IN ls1 ==>
   t_jgmt TS l1 ls2 post post
  ) ==>
  t_jgmt TS l ls2 pre post
Proof
rpt strip_tac >>
simp [t_jgmt_def] >>
rpt strip_tac >>
PAT_X_ASSUM ``t_jgmt TS l (ls1 UNION ls2) pre post``
              (fn thm => ASSUME_TAC (SIMP_RULE std_ss [t_jgmt_def] thm)) >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
rfs [] >>
Cases_on `TS.ctrl s' IN ls2` >- (
 metis_tac [weak_union2]
) >>
subgoal `TS.ctrl s' IN ls1` >- (
 metis_tac [weak_union, weak_ctrl_in]
) >>
QSPECL_X_ASSUM  ``!l1. _`` [`TS.ctrl s'`] >>
rfs [t_jgmt_def] >>
QSPECL_X_ASSUM  ``!TS. _`` [`s'`] >>
rfs [] >>
ASSUME_TAC (Q.SPECL [`TS`] weak_comp) >>
metis_tac []
QED


Theorem total_conj_rule:
 !TS.
  first_enc TS ==>
  !l ls pre post1 post2.
  t_jgmt TS l ls pre post1 ==>
  t_jgmt TS l ls pre post2 ==>
  t_jgmt TS l ls pre (\s. post1 s /\ post2 s)
Proof
rpt strip_tac >>
fs [t_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_unique]
QED


Definition loop_step_def:
 loop_step TS s var l le invariant C1 =
  let x:num = var s in
   (\s'. TS.weak ({l} UNION le) s s' /\
         (invariant s /\ C1 s) /\
         (TS.ctrl s' = l /\ invariant s' /\ var s' < x /\ var s' >= 0)
   )
End

val loop_fun_defn =
 Hol_defn "loop_fun" `
  loop_fun TS s var l le invariant C1  =
   let S' = loop_step TS s var l le invariant C1 in
    if S' = {} then s
    else let s' = (CHOICE S') in
     (loop_fun TS s' var l le invariant C1)
`;

(*
Defn.tgoal loop_fun_defn
*)
val (loop_fun_eqns, loop_fun_ind) = Defn.tprove(loop_fun_defn,
  fs [loop_step_def] >>
  WF_REL_TAC `measure (\(TS,s,var,l,le,invariant,C1). var s)` >>
  rpt strip_tac >>
  rfs [LET_DEF] >>
  Q.ABBREV_TAC `S' =  (\s'.
               TS.weak ({l} UNION le) s s' /\ (invariant s /\ C1 s) /\
               ((TS.ctrl s') = l) /\ invariant s' /\ var s' < var s)` >>
  ASSUME_TAC (ISPEC ``S':'a->bool`` pred_setTheory.CHOICE_DEF) >>
  rfs [] >>
  fs [Abbr `S'`, pred_setTheory.IN_ABS]
);


Definition total_loop_jgmt_def:
 total_loop_jgmt TS l le invariant C1 var =
  (~(l IN le) /\
   !x:num. t_jgmt TS l ({l} UNION le) (\s. invariant s /\ C1 s /\ var s = x)
        (\s. TS.ctrl s = l /\ invariant s /\ var s < x /\ var s >= 0))
End

(* Note that due to loop_fun_ind relating states s and s' at loop points,
 * s needs to be exposed also here. Either this can be explicitly specified
 * in the precondition of the conclusion, or the definition can be unfolded, like here *)
val loop_fun_ind_spec =
 Q.SPEC `\TS s var l le invariant C1.
          first_enc TS ==>
	  total_loop_jgmt TS l le invariant C1 var ==>
	  t_jgmt TS l le (\s. invariant s /\ ~C1 s) post ==>
	  (invariant s /\ TS.ctrl s = l) ==>
	  (?s'. TS.weak le s s' /\ post s')` loop_fun_ind;


val inductive_invariant_goal = fst $ dest_imp $ concl loop_fun_ind_spec;


val inductive_invariant = prove(``
  ^inductive_invariant_goal
``,

rpt strip_tac >>
fs [] >>
rpt strip_tac >>
Cases_on `~C1 s` >- (
  fs [t_jgmt_def]
) >>
(* We first prove that one iteration works (first antecedent of induction hypothesis):
 * OK since C1 holds in s, then use loop judgment to obtain
 * witness *)
subgoal `loop_step TS s var l le invariant C1 <> {}` >- (
  simp [loop_step_def, LET_DEF] >>
  fs [total_loop_jgmt_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`(var s):num`] >>
  fs [t_jgmt_def] >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  rfs [] >>
  fs [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  qexists_tac `s'':'a` >>
  fs [pred_setTheory.SPECIFICATION]
) >>
(* There first four antecedents of the induction hypothesis are now in place *)
fs [] >>
(* Let s' be the state at the next loop iteration *)
Q.ABBREV_TAC `S' = loop_step TS s var l le invariant C1` >>
Q.ABBREV_TAC `s' = CHOICE S'` >>
subgoal `loop_step TS s var l le invariant C1 s'` >- (
  fs [Abbr `s'`] >>
  ONCE_REWRITE_TAC [GSYM pred_setTheory.SPECIFICATION] >>
  metis_tac [pred_setTheory.CHOICE_DEF]
) >>
(* We then prove that the invariant is preserved and loop
 * point is l
 * (follows from s' being the result of a loop_step) *)
subgoal `invariant s' /\ (TS.ctrl s') = l` >- (
  fs [loop_step_def, LET_DEF]
) >>
fs [] >>
(* For both cases, weak_comp_thm is used to connect s to s'' via s'. *)
fs [loop_step_def, LET_DEF] >>
`TS.weak le s s''` suffices_by (
  metis_tac []
) >>
irule weak_comp >>
fs [] >>
qexistsl_tac [`{l}`, `s'`] >>
Q.SUBGOAL_THEN `l NOTIN le` (fn thm => fs [thm]) >- (
  fs [total_loop_jgmt_def, pred_setTheory.IN_SING]
)
);

(* Now just some final touches to get the theorem in the exact shape we want *)
val total_loop_rule_thm_tmp = MP loop_fun_ind_spec inductive_invariant;

Theorem total_loop_rule_thm:
 !TS.
  first_enc TS ==>
  !l le invariant C1 var post.
  total_loop_jgmt TS l le invariant C1 var ==>
  t_jgmt TS l le (\s. invariant s /\ ~C1 s) post ==>
  t_jgmt TS l le invariant post
Proof
metis_tac [t_jgmt_def, total_loop_rule_thm_tmp]
QED

val _ = export_theory();
