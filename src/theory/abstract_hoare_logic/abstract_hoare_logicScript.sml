open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

val _ = new_theory "abstract_hoare_logic";

(* Transition system *)
val _ = Datatype `abstract_model_t =
  <|(* Transition function *)
    trs : 'a -> 'a option;
    (* Weak transition relation *)
    weak : 'a -> ('b -> bool) -> 'a -> bool;
    (* A function to obtain the control state from a state.
     * This allows for isolating parts of the state that
     * the weak transition is provably oblivious to. *)
    pc : 'a -> 'b
   |>`;

(* An abstract model is a weak model if this property is fulfilled.
 * This is how the weak transition is forced to be related to
 * the single transition.  *)
val weak_model_def = Define `
  weak_model m =
    !ms ls ms'.
      (m.weak ms ls ms') =
        ?n.
          ((n > 0) /\
           (FUNPOW_OPT m.trs n ms = SOME ms') /\
           ((m.pc ms') IN ls)
          ) /\
          !n'.
            (((n' < n) /\ (n' > 0)) ==>
            ?ms''.
              (FUNPOW_OPT m.trs n' ms = SOME ms'') /\
              (~((m.pc ms'') IN ls))
            )`;


val weak_comp_thm = store_thm("weak_comp_thm",
``!m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms''.
  (m.weak ms (ls1 UNION ls2) ms') ==> (~((m.pc ms') IN ls2)) ==>
  (m.weak ms' ls2 ms'') ==> (m.weak ms ls2 ms'')``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
EXISTS_TAC ``n'+n:num`` >>
ASSUME_TAC (Q.SPECL [`m.trs`, `n'`, `n`, `ms`, `ms'`, `ms''`] FUNPOW_OPT_ADD_thm) >>
REV_FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
Cases_on `n'' < n'` >- (
  METIS_TAC [pred_setTheory.IN_UNION]
) >>
Cases_on `n'' = n'` >- (
  METIS_TAC []
) >>
SUBGOAL_THEN ``n'':num = (n''-n')+n'`` ASSUME_TAC >- (FULL_SIMP_TAC arith_ss []) >>
QSPECL_X_ASSUM ``!n''.((n'' < n:num) /\ (n'' > 0)) ==> P`` [`n''-n':num`] >>
REV_FULL_SIMP_TAC arith_ss [] >>
ASSUME_TAC (Q.SPECL [`m.trs`, `n'`, `n''-n'`, `ms`, `ms'`, `ms'''`] FUNPOW_OPT_ADD_thm) >>
REV_FULL_SIMP_TAC arith_ss []
);


val weak_unique_thm = store_thm("weak_unique_thm",
``!m.
  (weak_model m) ==>
  !ms ls ms' ms''.
  (m.weak ms ls ms') ==>
  (m.weak ms ls ms'') ==>
  (ms' = ms'')
``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
Q.SUBGOAL_THEN `n = n'` (FULLSIMP_BY_THM arith_ss)  >>
Cases_on `n < n'` >- (
   QSPECL_X_ASSUM ``!n'':num.(n'' < n' /\ n'' > 0) ==> P`` [`n:num`] >>
   REV_FULL_SIMP_TAC std_ss [] 
) >>
Cases_on `n > n'` >- (
   QSPECL_X_ASSUM ``!n'':num.(n'' < n /\ n'' > 0) ==> P`` [`n':num`] >>
   REV_FULL_SIMP_TAC arith_ss [] 
) >>
FULL_SIMP_TAC arith_ss [] 
);

val weak_union_thm = store_thm("weak_union_thm",``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms'.
  (m.weak ms (ls1 UNION ls2) ms') ==>
  (~ ((m.pc ms') IN ls1)) ==>
  (m.weak ms ls2 ms')``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
Q.EXISTS_TAC `n` >>
METIS_TAC [pred_setTheory.IN_UNION]
);

val weak_union2_thm = store_thm("weak_union2_thm",``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms'.
  (m.weak ms (ls1 UNION ls2) ms') ==>
  (((m.pc ms') IN ls2)) ==>
  (m.weak ms ls2 ms')``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
Q.EXISTS_TAC `n` >>
METIS_TAC [pred_setTheory.IN_UNION]
);

val weak_union_singleton_thm = prove(``
  !m.
  weak_model m ==>
  !ms l1 ls2 ms'.
  (m.weak ms ({l1} UNION ls2) ms') ==>
  ((m.pc ms') <> l1) ==>
  (m.weak ms ls2 ms')``,

METIS_TAC [weak_union_thm, pred_setTheory.IN_SING]
);

val weak_singleton_pc_thm = prove(``
  !m.
  weak_model m ==>
  !ms e ms'.
  (m.weak ms {e} ms') ==> ((m.pc ms') = e)``,

METIS_TAC [weak_model_def, pred_setTheory.IN_SING]
);


val weak_pc_in_thm = store_thm("weak_pc_in_thm",
  ``!m.
    weak_model m ==>
    !ms ls ms'.
    (m.weak ms ls ms') ==> ((m.pc ms') IN ls)``,

METIS_TAC [weak_model_def]
);

val weak_union_pc_not_in_thm = store_thm("weak_union_pc_not_in_thm",
  ``!m.
    weak_model m ==>
    !ms e ls1 ls2 ms'.
    (m.weak ms (ls1 UNION ls2) ms') ==>
    (~((m.pc ms') IN ls2)) ==>
    (m.weak ms ls1 ms')``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_model_def] >>
METIS_TAC [pred_setTheory.IN_UNION]
);



(* Judgment of the logic *)
(* Pre and post usually have conditions on execution mode and code in memory,
   also post is usually a map that depends on the end state address *)
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
  REPEAT STRIP_TAC >>
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
    !x. abstract_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms /\ var ms = x:num)
          (\ms. m.pc ms = l /\ invariant ms /\ var ms < x /\ var ms >= 0))
`;

(* Note that due to loop_fun_ind relating states ms and ms' at loop points,
 * ms needs to be exposed also here. Either this can be explicitly specified
 * in the precondition of the conclusion, or the definition can be unfolded, like here *)
val loop_fun_ind_spec =
  Q.SPEC `\m ms var l le invariant C1.
	   weak_model m ==>
	   abstract_loop_jgmt m l le invariant C1 var ==>
	   abstract_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
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
);

(* Now just some final touches to get the theorem in the exact shape we want *)
val abstract_loop_rule_tmp_thm = MP loop_fun_ind_spec inductive_invariant;

val abstract_loop_rule_thm = store_thm("abstract_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    abstract_loop_jgmt m l le invariant C1 var ==>
    abstract_jgmt m l le (\ms. invariant ms /\ ~C1 ms) post ==>
    abstract_jgmt m l le invariant post``,

metis_tac [abstract_jgmt_def, abstract_loop_rule_tmp_thm]
);

val _ = export_theory();
