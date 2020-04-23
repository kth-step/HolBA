open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

val _ = new_theory "bin_hoare_logic";

(* Generalization of exec to label *)
val _ = Datatype `bin_model_t =
  <|(* A function to obtain a state option from a state via
     * execution (transition) *)
    trs : 'a -> 'a option;
    (* A function to determine whether a transition between two
     * states is OK, through using a set of labels for which
     * execution must halt if reached, meaning they cannot be
     * touched in any intermediate step *)
    weak : 'a -> ('b -> bool) -> 'a -> bool;
    (* A function to obtain the program counter from a state *)
    pc : 'a -> 'b
   |>`;

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


val weak_comp_thm = prove(``
  !m.
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


val weak_unique_thm = prove(``
  !m.
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

val weak_union_thm = prove(``
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

val weak_union2_thm = prove(``
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


val weak_pc_in_thm = prove(``
  !m.
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



(* Definition of the triple *)
(* Pre and post usually have conditions on execution mode and code in memory *)
(* also post is usually a map that depends on the end state address *)
val weak_triple_def = Define `
  weak_triple m (l:'a) (ls:'a->bool) pre post =
  !ms .
   ((m.pc ms) = l) ==> (pre ms) ==>
   ?ms'. ((m.weak ms ls ms') /\
    (post ms'))
`;


val weak_case_rule_thm = prove(``
!m l ls pre post C1.
  weak_triple m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  weak_triple m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  weak_triple m l ls pre post
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_triple_def] >>
METIS_TAC []
);

val weak_weakening_rule_thm =
  store_thm("weak_weakening_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    weak_triple m l ls pre1 post1 ==>
    weak_triple m l ls pre2 post2
  ``,

SIMP_TAC std_ss [weak_triple_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_pc_in_thm]
);



val weak_subset_rule_thm =
 store_thm("weak_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. ((post ms) ==> (~((m.pc ms) IN ls2)))) ==>
    weak_triple m l (ls1 UNION ls2) pre post ==>
    weak_triple m l ls1 pre post``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [weak_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!x. _`` [`ms`] >>
METIS_TAC [weak_union_pc_not_in_thm]
);


val weak_seq_rule_thm = store_thm("weak_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    weak_triple m l (ls1 UNION ls2) pre post ==>
    (!l1. (l1 IN ls1) ==>
    (weak_triple m l1 ls2 post post)) ==>
    weak_triple m l ls2 pre post``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [weak_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``(weak_triple m l (ls1 UNION ls2) pre  post)``
              (fn thm => ASSUME_TAC (SIMP_RULE std_ss [weak_triple_def] thm)) >>
QSPECL_X_ASSUM ``!x.P`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `(m.pc ms') IN ls2` >- (
  METIS_TAC [weak_union2_thm]
) >>
Q.SUBGOAL_THEN `(m.pc ms') IN ls1` ASSUME_TAC >- (
  METIS_TAC [weak_union_thm, weak_pc_in_thm]
) >>
QSPECL_X_ASSUM  ``!l1. _`` [`m.pc ms'`] >>
REV_FULL_SIMP_TAC std_ss [weak_triple_def] >>
QSPECL_X_ASSUM  ``!m. _`` [`ms'`] >>
REV_FULL_SIMP_TAC std_ss[] >>
ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
METIS_TAC []
);


val weak_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  weak_triple m l ls pre post1 ==>
  weak_triple m l ls pre post2 ==>
  weak_triple m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_triple_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_unique_thm]
);



val weak_loop_step_def = Define `
 weak_loop_step m ms var l le invariant C1 =
 let x:num = var ms in
 (\ms'. (m.weak ms ({l} UNION le) ms') /\
       ((invariant ms) /\ (C1 ms)) /\
       (((m.pc ms')=l) /\ (invariant ms') /\ ((var ms') < x) /\ ((var ms') >= 0))
       )
       `;

val loop_fun_defn =
       Hol_defn "loop_fun" `
loop_fun m ms var l le invariant C1  =
let MS' = weak_loop_step m ms var l le invariant C1 in
if MS' = {} then ms
else let ms' = (CHOICE MS') in
  (loop_fun m ms' var l le invariant C1)
`;

(*
Defn.tgoal loop_fun_defn
*)
val (loop_fun_eqns, loop_fun_ind) = Defn.tprove(loop_fun_defn,
  FULL_SIMP_TAC std_ss [weak_loop_step_def] >>
  WF_REL_TAC `measure (\(m, ms,var,l,le,invariant,C1). var ms)` >>
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
  Q.ABBREV_TAC `MS' =  (\ms'.
               m.weak ms ({l} UNION le) ms' /\ (invariant ms /\ C1 ms) /\
               ((m.pc ms') = l) /\ invariant ms' /\ var ms' < var ms)` >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `MS'`, pred_setTheory.IN_ABS]
);


val weak_loop_contract_def = Define `
  weak_loop_contract m l le invariant C1 var =
    (~(l IN le)) /\
    (!x. (weak_triple m l ({l} UNION le) (\ms. (invariant ms) /\ (C1 ms) /\ ((var ms) = x:num))
         (\ms.(((m.pc ms)=l) /\ (invariant ms) /\ ((var ms) < x) /\ ((var ms) >= 0)))))
`;

val inductive_invariant_goal = (fst o dest_imp o concl ) (
Q.SPEC `(\m ms var l le invariant C1.
weak_model m ==>
weak_loop_contract m l le invariant C1 var ==>
weak_triple m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
((invariant ms) /\ ((m.pc ms) = l) /\ (C1 ms)) ==>
 (?ms'. ((m.weak ms le ms') /\ (post ms'))))` loop_fun_ind);


val inductive_invariant_thm = prove(``
^inductive_invariant_goal
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
(* We first prove that one iteration works *)
SUBGOAL_THEN ``(weak_loop_step m ms var l le invariant C1) <> {}`` ASSUME_TAC  >- (
  SIMP_TAC std_ss [weak_loop_step_def, LET_DEF] >>
  FULL_SIMP_TAC std_ss [weak_loop_contract_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`(var (ms)):num`] >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  QSPECL_X_ASSUM ``!x. _`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  EXISTS_TAC ``ms'':'a`` >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
FULL_SIMP_TAC std_ss [] >>

Q.ABBREV_TAC `MS' = (weak_loop_step m ms var l le invariant C1)` >>
Q.ABBREV_TAC `ms' = CHOICE MS'` >>

(* We prove that the invariant is preserved *)
SUBGOAL_THEN ``(weak_loop_step m ms var l le invariant C1) ms'`` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [Abbr `ms'`] >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF) >>
  REV_FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
Q.SUBGOAL_THEN `invariant ms'` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [ weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(m.pc ms') = l` ASSUME_TAC >- (
  FULL_SIMP_TAC std_ss [ weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>

(* If we exit the loop *)
Cases_on `~ (C1 ms')` >- (
  (FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]) >>
  (FULL_SIMP_TAC std_ss [weak_triple_def]) >>
  QSPECL_X_ASSUM  ``!x. _`` [`ms'`] >>
  (REV_FULL_SIMP_TAC std_ss []) >>
  ASSUME_TAC (Q.SPECL [`m`] weak_comp_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!x. _`` [`ms`, `{l}`, `le`, `ms'`, `ms''`] >>
  REV_FULL_SIMP_TAC (std_ss) [SINGLETONS_UNION_thm] >>
  Q.SUBGOAL_THEN `l NOTIN le` (FULLSIMP_BY_THM std_ss) >- (
    FULL_SIMP_TAC std_ss [weak_loop_contract_def, pred_setTheory.IN_SING]
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
    FULL_SIMP_TAC std_ss [weak_loop_contract_def, pred_setTheory.IN_SING]
  ) >>
  METIS_TAC []
);




val invariant_rule_tmp_thm = 
MP 
(Q.SPEC `(\m ms var l le invariant C1.
weak_model m ==>
weak_loop_contract m l le invariant C1 var ==>
weak_triple m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
((invariant ms) /\ ((m.pc ms) = l) /\ (C1 ms)) ==>
 (?ms'. ((m.weak ms le ms') /\ (post ms'))))` loop_fun_ind) inductive_invariant_thm;

val weak_invariant_rule_thm = store_thm("weak_invariant_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    weak_loop_contract m l le invariant C1 var ==>
    weak_triple m l le (\ms. (invariant ms) /\ (~(C1 ms))) post ==>
    weak_triple m l le invariant post``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [weak_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`m`, `ms`, `var`, `l`, `le`, `invariant`, `C1`] invariant_rule_tmp_thm) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `C1 ms` >- (
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ms'`>>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [weak_triple_def] 
);

val _ = export_theory();
