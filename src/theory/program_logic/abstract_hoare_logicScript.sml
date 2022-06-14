open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open transition_systemTheory;

val _ = new_theory "total_program_logic";

(* Judgment of the total-correctness logic *)
Definition t_jgmt_def:
 t_jgmt TS (l:'a) (ls:'a->bool) pre post =
  !s.
   TS.ctrl s = l ==>
   pre s ==>
   ?s'. TS.weak s ls s' /\ post s'
End

(* Judgment of the total-correctness logic, adjusted for
 * non-determinism *)
Definition t_nondet_jgmt_def:
 t_nondet_jgmt TS (l:'a) (ls:'a->bool) pre post =
  !s.
   TS.ctrl s = l ==>
   pre s ==>
   TS.weak s ls <> {} /\ (!s'. TS.weak s ls s' /\ post s')
End


(* TODO: Can this be rephrased better?
 * Antecedents guarantee swapping transition system of ANY contract. *)
Theorem total_comp_rule_thm:
 !TS TS'.
  first_enc TS ==>
  first_enc TS' ==>
  (!s ls s'. TS.weak s ls s' ==> TS'.weak s ls s') ==>
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
QSPECL_X_ASSUM ``!s ls s'. _`` [`s`, `ls`, `s'`] >>
rfs [] >>
Q.EXISTS_TAC `s'` >>
fs []
QED

Theorem total_nondet_comp_rule_thm:
 !TS TS'.
  first_enc TS ==>
  first_enc TS' ==>
  (!s ls s'. TS.weak s ls s' ==> TS'.weak s ls s') ==>
  (!s l. (TS'.ctrl s = l)  ==> (TS.ctrl s = l)) ==>
  !l ls pre post.
   t_nondet_jgmt TS l ls pre post ==>
   t_nondet_jgmt TS' l ls pre post
Proof
rpt strip_tac >>
fs [t_nondet_jgmt_def] >>
rpt strip_tac >> (
 QSPECL_X_ASSUM ``!s. _`` [`s`] >>
 QSPECL_X_ASSUM ``!s. _`` [`s`] >>
 subgoal `TS'.weak s ls <> {}` >- (
  gs [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  QSPECL_X_ASSUM ``!s'. _`` [`s'`] >>
  gs [] >>
  res_tac >>
  metis_tac [pred_setTheory.MEMBER_NOT_EMPTY, pred_setTheory.IN_APP]
  cheat
 ) >>
 gs []

)
QED

val abstract_case_rule_thm = prove(``
!m l ls pre post C1.
  t_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  t_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  t_jgmt m l ls pre post
``,

rpt strip_tac >>
fs [t_jgmt_def] >>
metis_tac []
);

val abstract_conseq_rule_thm =
  store_thm("abstract_conseq_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    t_jgmt m l ls pre1 post1 ==>
    t_jgmt m l ls pre2 post2
  ``,

rpt strip_tac >>
fs [t_jgmt_def] >>
metis_tac [weak_pc_in_thm]
);



val abstract_subset_rule_thm =
 store_thm("abstract_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. ((post ms) ==> (~((m.pc ms) IN ls2)))) ==>
    t_jgmt m l (ls1 UNION ls2) pre post ==>
    t_jgmt m l ls1 pre post``,

rpt strip_tac >>
REV_FULL_SIMP_TAC std_ss [t_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
METIS_TAC [weak_union_pc_not_in_thm]
);


val abstract_seq_rule_thm = store_thm("abstract_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    t_jgmt m l (ls1 UNION ls2) pre post ==>
    (!l1.
     l1 IN ls1 ==>
     t_jgmt m l1 ls2 post post
    ) ==>
    t_jgmt m l ls2 pre post``,

rpt strip_tac >>
SIMP_TAC std_ss [t_jgmt_def] >>
rpt strip_tac >>
PAT_X_ASSUM ``t_jgmt m l (ls1 UNION ls2) pre post``
              (fn thm => ASSUME_TAC (SIMP_RULE std_ss [t_jgmt_def] thm)) >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `m.pc ms' IN ls2` >- (
  METIS_TAC [weak_union2_thm]
) >>
subgoal `m.pc ms' IN ls1` >- (
  METIS_TAC [weak_union_thm, weak_pc_in_thm]
) >>
QSPECL_X_ASSUM  ``!l1. _`` [`m.pc ms'`] >>
REV_FULL_SIMP_TAC std_ss [t_jgmt_def] >>
QSPECL_X_ASSUM  ``!m. _`` [`ms'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
METIS_TAC []
);


val abstract_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  t_jgmt m l ls pre post1 ==>
  t_jgmt m l ls pre post2 ==>
  t_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

rpt strip_tac >>
FULL_SIMP_TAC std_ss [t_jgmt_def] >>
rpt strip_tac >>
METIS_TAC [weak_unique_thm]
);



val loop_step_def = Define `
  loop_step m ms var l le invariant C1 =
    let x:num = var ms in
    (\ms'. m.weak ms ({l} UNION le) ms' /\
	   (invariant ms /\ C1 ms) /\
	   ((m.pc ms' = l) /\ invariant ms' /\ (var ms' < x) /\ (var ms' >= 0))
    )
`;

val loop_fun_defn =
  Hol_defn "loop_fun" `
    loop_fun m ms var l le invariant C1  =
      let MS' = loop_step m ms var l le invariant C1 in
      if MS' = {} then ms
      else let ms' = (CHOICE MS') in
	(loop_fun m ms' var l le invariant C1)
`;

(*
Defn.tgoal loop_fun_defn
*)
val (loop_fun_eqns, loop_fun_ind) = Defn.tprove(loop_fun_defn,
  FULL_SIMP_TAC std_ss [loop_step_def] >>
  WF_REL_TAC `measure (\(m,ms,var,l,le,invariant,C1). var ms)` >>
  rpt strip_tac >>
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
  Q.ABBREV_TAC `MS' =  (\ms'.
               m.weak ms ({l} UNION le) ms' /\ (invariant ms /\ C1 ms) /\
               ((m.pc ms') = l) /\ invariant ms' /\ var ms' < var ms)` >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `MS'`, pred_setTheory.IN_ABS]
);


val abstract_loop_jgmt_def = Define `
  abstract_loop_jgmt m l le invariant C1 var =
    (~(l IN le) /\
    !x. t_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms /\ var ms = x:num)
          (\ms. m.pc ms = l /\ invariant ms /\ var ms < x /\ var ms >= 0))
`;

(* Note that due to loop_fun_ind relating states ms and ms' at loop points,
 * ms needs to be exposed also here. Either this can be explicitly specified
 * in the precondition of the conclusion, or the definition can be unfolded, like here *)
val loop_fun_ind_spec =
  Q.SPEC `\m ms var l le invariant C1.
	   weak_model m ==>
	   abstract_loop_jgmt m l le invariant C1 var ==>
	   t_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
	   (invariant ms /\ m.pc ms = l) ==>
	   (?ms'. m.weak ms le ms' /\ post ms')` loop_fun_ind;


val inductive_invariant_goal = fst $ dest_imp $ concl loop_fun_ind_spec;


val inductive_invariant = prove(``
  ^inductive_invariant_goal
``,

rpt strip_tac >>
fs [] >>
rpt strip_tac >>
Cases_on `~C1 ms` >- (
  fs [t_jgmt_def]
) >>
(* We first prove that one iteration works (first antecedent of induction hypothesis):
 * OK since C1 holds in ms, then use loop judgment to obtain
 * witness *)
subgoal `loop_step m ms var l le invariant C1 <> {}` >- (
  simp [loop_step_def, LET_DEF] >>
  fs [abstract_loop_jgmt_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`(var ms):num`] >>
  fs [t_jgmt_def] >>
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
);

(* Now just some final touches to get the theorem in the exact shape we want *)
val abstract_loop_rule_tmp_thm = MP loop_fun_ind_spec inductive_invariant;

val abstract_loop_rule_thm = store_thm("abstract_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    abstract_loop_jgmt m l le invariant C1 var ==>
    t_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
    t_jgmt m l le invariant post``,

metis_tac [t_jgmt_def, abstract_loop_rule_tmp_thm]
);

val _ = export_theory();
