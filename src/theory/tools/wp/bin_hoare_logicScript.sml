open HolKernel Parse boolLib bossLib;

val _ = new_theory "bin_hoare_logic";

(* Utility tactics *)
fun QSPECL_ASSUM pat ls = PAT_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun QSPECL_X_ASSUM pat ls = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (Q.SPECL ls thm));
fun FULLSIMP_BY_THM ss thm = FULL_SIMP_TAC ss [thm];

(* Utility theorems *)
val FUNPOW_OPT_ADD_thm = prove(``
  !f n n' ms ms' ms''.
  (FUNPOW_OPT f n ms = SOME ms') ==>  (FUNPOW_OPT f n' ms' = SOME ms'') ==>  (FUNPOW_OPT f (n'+n) ms = SOME ms'')
``,
  METIS_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
);

val IN_UNION_ABSORB_thm = prove(``! l ls. (l IN ls) ==> (({l} UNION ls) = ls)``,
  METIS_TAC [pred_setTheory.ABSORPTION, GSYM pred_setTheory.INSERT_SING_UNION]
);

val SINGLETONS_UNION_thm = prove(``! l e. ({l} UNION {e}) = {l;e}``,
  METIS_TAC [pred_setTheory.INSERT_SING_UNION]
);



(* Generalization of exec to label *)
val rel_is_weak_trs_def = Define `
  rel_is_weak_trs rel tr pc = ! ms ls ms' . (rel ms ls ms') =
  ?n . ((n > 0) /\ (FUNPOW_OPT tr n ms = SOME ms') /\ ((pc ms') IN ls)) /\
    !n'. (((n' < n) /\ (n' > 0)) ==> ?ms''.(FUNPOW_OPT tr n' ms = SOME ms'') /\ (~((pc ms'') IN ls)))`;

val weak_trs_comp_thm = prove(``
!rel tr pc. (rel_is_weak_trs rel tr pc) ==>
!ms ls1 ls2 ms' ms''.
(rel ms (ls1 UNION ls2) ms') ==> (~ ((pc ms') IN ls2)) ==>
(rel ms' ls2 ms'') ==> (rel ms ls2 ms'')
``,
REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [rel_is_weak_trs_def] >>
EXISTS_TAC ``n'+n:num`` >>
ASSUME_TAC (Q.SPECL [`tr`, `n'`, `n`, `ms`, `ms'`, `ms''`] FUNPOW_OPT_ADD_thm) >>
REV_FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
(Cases_on `n'' < n'`) >-
(
  METIS_TAC [pred_setTheory.IN_UNION]
) >>
(Cases_on `n'' = n'`) >- ( METIS_TAC [] ) >>
SUBGOAL_THEN ``n'':num = (n''-n')+n'`` ASSUME_TAC >- (FULL_SIMP_TAC arith_ss []) >>
QSPECL_X_ASSUM ``∀n''.((n'' < n:num) ∧ (n'' > 0)) ==> P`` [`n''-n':num`] >>
REV_FULL_SIMP_TAC arith_ss [] >>
ASSUME_TAC (Q.SPECL [`tr`, `n'`, `n''-n'`, `ms`, `ms'`, `ms'''`] FUNPOW_OPT_ADD_thm) >>
REV_FULL_SIMP_TAC arith_ss []
);


val weak_trs_unique_thm = prove(``
  !rel tr pc. (rel_is_weak_trs rel tr pc) ==>
  !ms ls ms' ms''. (rel ms ls ms') ==> (rel ms ls ms'') ==> (ms' = ms'')
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [rel_is_weak_trs_def] >>
  Q.SUBGOAL_THEN `n = n'` (FULLSIMP_BY_THM arith_ss)  >>
  (Cases_on `n < n'`) >-
  (
     QSPECL_X_ASSUM ``!n'':num.(n'' < n' ∧ n'' > 0) ⇒ P`` [`n:num`] >>
     REV_FULL_SIMP_TAC std_ss [] 
  ) >>
  (Cases_on `n > n'`) >-
  (
     QSPECL_X_ASSUM ``!n'':num.(n'' < n ∧ n'' > 0) ⇒ P`` [`n':num`] >>
     REV_FULL_SIMP_TAC arith_ss [] 
  ) >>
  FULL_SIMP_TAC arith_ss [] 
);

val weak_trs_union_thm = prove(``
  !rel tr pc. (rel_is_weak_trs rel tr pc) ==>
  !ms ls1 ls2 ms'.
  (rel ms (ls1 UNION ls2) ms') ==> (~ ((pc ms') IN ls1)) ==> (rel ms ls2 ms')
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [rel_is_weak_trs_def] >>
  Q.EXISTS_TAC `n` >>
  METIS_TAC [pred_setTheory.IN_UNION]
);

val weak_trs_union_singleton_thm = prove(``
  !rel tr pc. (rel_is_weak_trs rel tr pc) ==>
  !ms l1 ls2 ms'.
  (rel ms ({l1} UNION ls2) ms') ==> ((pc ms') <> l1) ==> (rel ms ls2 ms')
``,
METIS_TAC [weak_trs_union_thm, pred_setTheory.IN_SING]
);

val weak_trs_singleton_pc_thm = prove(``
!rel tr pc. !ms e ms'.
(rel_is_weak_trs rel tr pc) ==> (rel ms {e} ms') ==> ((pc ms') = e)
``,
  METIS_TAC[rel_is_weak_trs_def, pred_setTheory.IN_SING]
);


val weak_trs_in_pc_thm = prove(``
  !rel tr pc. !ms ls ms'. (rel_is_weak_trs rel tr pc) ==> (rel ms ls ms') ==> ((pc ms') IN ls)
``,
  METIS_TAC [rel_is_weak_trs_def]
);

val weak_trs_union_not_in_pc_thm = prove(``
 !rel tr pc. !ms e ls1 ls2 ms'.
 (rel_is_weak_trs rel tr pc) ==> (rel ms (ls1 UNION ls2) ms') ==> (~((pc ms') IN ls2)) ==>
 (rel ms ls1 ms')
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [rel_is_weak_trs_def] >>
  METIS_TAC [pred_setTheory.IN_UNION]
);



(* Definition of the triple *)
(* Pre and post usually have conditions on execution mode and code in memory *)
(* also post is usually a map that depends on the end state address *)
val weak_trs_triple_def = Define `
  weak_trs_triple rel pc (l:'a) (ls:'a->bool) pre post =
  ! ms .
   ((pc ms) = l) ==> (pre ms) ==>
   ?ms'. ((rel ms ls ms') /\
    (post ms'))
`;


val weak_trs_case_rule_thm = prove(``
!rel pc l ls pre post C1.
  (weak_trs_triple rel pc l ls (\ms. (pre ms) /\ (C1 ms))  post) ==>
  (weak_trs_triple rel pc l ls (\ms. (pre ms) /\ (~(C1 ms))) post) ==>
  (weak_trs_triple rel pc l ls pre post)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [weak_trs_triple_def] >>
  METIS_TAC []
);

val weak_trs_weak_rule_thm = prove(``
  !rel tr pc l ls pre1 pre2 post1 post2 .
  (rel_is_weak_trs rel tr pc) ==>
  (!ms. ((pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
  (!ms. ((pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
  (weak_trs_triple rel pc l ls pre1 post1) ==>
  (weak_trs_triple rel pc l ls pre2 post2)
``,
  SIMP_TAC std_ss [weak_trs_triple_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [weak_trs_in_pc_thm]
);



val weak_trs_subset_rule_thm = prove(``
  !rel tr pc l ls1 ls2 pre post .
  (rel_is_weak_trs rel tr pc) ==>
  (!ms. ((post ms) ==> (~((pc ms) IN ls2)))) ==>
  (weak_trs_triple rel pc l (ls1 UNION ls2) pre post) ==>
  (weak_trs_triple rel pc l ls1 pre post)
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [weak_trs_triple_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!x.P`` [`ms`] >>
  METIS_TAC [weak_trs_union_not_in_pc_thm]
);



val weak_trs_seq_rule_thm = prove(``
!rel tr pc.
!l l1 ls2 pre post.
(rel_is_weak_trs rel tr pc) ==>
(weak_trs_triple rel pc l ({l1} UNION ls2) pre post) ==>
(weak_trs_triple rel pc l1 ls2 post post) ==>
(weak_trs_triple rel pc l ls2 pre post)
``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [weak_trs_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``(weak_trs_triple rel pc l ({l1} UNION ls2) pre  post)``
              (fn thm => ASSUME_TAC (SIMP_RULE std_ss [weak_trs_triple_def] thm)) >>
QSPECL_X_ASSUM ``!x.P`` [`ms`] >>
REV_FULL_SIMP_TAC std_ss [] >>
(Cases_on `(pc ms') <> l1`) >-
(
  METIS_TAC [weak_trs_union_singleton_thm]
) >>
FULL_SIMP_TAC std_ss [] >>
(Cases_on `l1 IN ls2`) >-
(
  METIS_TAC [IN_UNION_ABSORB_thm]
) >>
FULL_SIMP_TAC std_ss [weak_trs_triple_def] >>
QSPECL_X_ASSUM  ``!m.P`` [`ms'`] >>
REV_FULL_SIMP_TAC std_ss[] >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`] weak_trs_comp_thm) >>
METIS_TAC []
);

val weak_trs_conj_rule_thm = prove(``
! rel tr pc. !l ls pre post1 post2.
(rel_is_weak_trs rel tr pc) ==>
(weak_trs_triple rel pc l ls pre post1) ==>
(weak_trs_triple rel pc l ls pre post2) ==>
(weak_trs_triple rel pc l ls pre (\ms. (post1 ms) /\ (post2 ms)))
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_trs_triple_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_trs_unique_thm]
);



val weak_loop_step_def = Define `
 weak_loop_step rel pc ms var l e invariant C1 =
 let x:num = var ms in
 (\ms'. (rel ms {l; e} ms') /\
       ((invariant ms) /\ (C1 ms)) /\
       (((pc ms')=l) /\ (invariant ms') /\ ((var ms') < x) /\ ((var ms') >= 0))
       )
       `;

val loop_fun_defn =
       Hol_defn "loop_fun" `
loop_fun rel pc ms var l e invariant C1  =
let MS' = weak_loop_step rel pc ms var l e invariant C1 in
if MS' = ∅ then ms
else let ms' = (CHOICE MS') in
  (loop_fun rel pc ms' var l e invariant C1)
`;

(*
Defn.tgoal loop_fun_defn
*)
val (loop_fun_eqns, loop_fun_ind) = Defn.tprove(loop_fun_defn,
  FULL_SIMP_TAC std_ss [weak_loop_step_def] >>
  WF_REL_TAC `measure (\(rel, pc, ms,var,l,e,invariant,C1). var ms)` >>
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
  Q.ABBREV_TAC `MS' =  (λms'.
               rel ms {l; e} ms' ∧ (invariant ms ∧ C1 ms) ∧
               ((pc ms') = l) ∧ invariant ms' ∧ var ms' < var ms)` >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF)  >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `MS'`, pred_setTheory.IN_ABS]
);


val weak_loop_contract_def = Define `
weak_loop_contract rel pc l e invariant C1 var =
(l <> e) /\
(!x. (weak_trs_triple rel pc l {l; e} (\ms. (invariant ms) /\ (C1 ms) /\ ((var ms) = x:num))
     (\ms.(((pc ms)=l) /\ (invariant ms) /\ ((var ms) < x) /\ ((var ms) >= 0)))))
`;

val inductive_invariant_goal = (fst o dest_imp o concl ) (
Q.SPEC `(\rel pc ms var l e invariant C1.
(rel_is_weak_trs rel tr pc) ==>
(weak_loop_contract rel pc l e invariant C1 var) ==>
(weak_trs_triple rel pc l {e} (\ms. (invariant ms) /\ (~(C1 ms))) post) ==>
((invariant ms) /\ ((pc ms) = l) /\ (C1 ms)) ==>
 (?ms'. ((rel ms {e} ms') ∧ (post ms'))))` loop_fun_ind);

val inductive_invariant_thm = prove(``
^inductive_invariant_goal
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
(* We first prove that one iteration works *)
SUBGOAL_THEN ``(weak_loop_step rel pc ms var l e invariant C1) ≠ ∅`` ASSUME_TAC  >-
(
  SIMP_TAC std_ss [weak_loop_step_def, LET_DEF] >>
  FULL_SIMP_TAC std_ss [weak_loop_contract_def] >>
  QSPECL_X_ASSUM ``!x.P`` [`(var (ms)):num`] >>
  FULL_SIMP_TAC std_ss [weak_trs_triple_def] >>
  QSPECL_X_ASSUM ``!x.P`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
  EXISTS_TAC ``ms'':'a`` >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
FULL_SIMP_TAC std_ss [] >>

Q.ABBREV_TAC `MS' = (weak_loop_step rel pc ms var l e invariant C1)` >>
Q.ABBREV_TAC `ms' = CHOICE MS'` >>

(* We prove that the invariant is preserved *)
SUBGOAL_THEN ``(weak_loop_step rel pc ms var l e invariant C1) ms'`` ASSUME_TAC >-
(
  FULL_SIMP_TAC std_ss [Abbr `ms'`] >>
  ASSUME_TAC (ISPEC ``MS':'a->bool`` pred_setTheory.CHOICE_DEF) >>
  REV_FULL_SIMP_TAC std_ss [pred_setTheory.SPECIFICATION]
) >>
Q.SUBGOAL_THEN `invariant ms'` ASSUME_TAC >-
(
  FULL_SIMP_TAC std_ss [ weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(pc ms') = l` ASSUME_TAC >-
(
  FULL_SIMP_TAC std_ss [ weak_loop_step_def, LET_DEF]
) >>
FULL_SIMP_TAC std_ss [] >>

(* If we exit the loop *)
(Cases_on `~ (C1 ms')`) >-
(
  (FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF]) >>
  (FULL_SIMP_TAC std_ss [weak_trs_triple_def]) >>
  QSPECL_X_ASSUM  ``!x.P`` [`ms'`] >>
  (REV_FULL_SIMP_TAC std_ss []) >>
  ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`] weak_trs_comp_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!x.P`` [`ms`, `{l}`, `{e}`, `ms'`, `ms''`] >>
  REV_FULL_SIMP_TAC (std_ss) [SINGLETONS_UNION_thm] >>
  Q.SUBGOAL_THEN `l ∉ {e}` (FULLSIMP_BY_THM std_ss) >- (
    FULL_SIMP_TAC std_ss [weak_loop_contract_def, pred_setTheory.IN_SING]
  ) >>
  METIS_TAC [weak_trs_singleton_pc_thm]
) >>

(FULL_SIMP_TAC std_ss [] ) >>
(FULL_SIMP_TAC std_ss [weak_loop_step_def, LET_DEF] ) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`] weak_trs_comp_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!x.P`` [`ms`, `{l}`, `{e}`, `ms'`, `ms''`] >>
REV_FULL_SIMP_TAC (std_ss) [SINGLETONS_UNION_thm] >>
  Q.SUBGOAL_THEN `l ∉ {e}` (FULLSIMP_BY_THM std_ss) >- (
    FULL_SIMP_TAC std_ss [weak_loop_contract_def, pred_setTheory.IN_SING]
  ) >>
  METIS_TAC [weak_trs_singleton_pc_thm]
);


val invariant_rule_tmp_thm = 
MP 
(Q.SPEC `(\rel pc ms var l e invariant C1.
(rel_is_weak_trs rel tr pc) ==>
(weak_loop_contract rel pc l e invariant C1 var) ==>
(weak_trs_triple rel pc l {e} (\ms. (invariant ms) /\ (~(C1 ms))) post) ==>
((invariant ms) /\ ((pc ms) = l) /\ (C1 ms)) ==>
 (?ms'. ((rel ms {e} ms') ∧ (post ms'))))` loop_fun_ind) inductive_invariant_thm;

val weak_trs_invariant_rule_thm = prove(``
!rel tr pc. ! l e invariant C1 var post.
(rel_is_weak_trs rel tr pc) ==>
(weak_loop_contract rel pc l e invariant C1 var) ==>
(weak_trs_triple rel pc l {e} (\ms. (invariant ms) /\ (~(C1 ms))) post) ==>
(weak_trs_triple rel pc l {e} invariant post)
``,
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [weak_trs_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`rel`, `pc`, `ms`, `var`, `l`, `e`, `invariant`, `C1`] invariant_rule_tmp_thm) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
(Cases_on `C1 ms`) >-
(
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ms'`>>
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [weak_trs_singleton_pc_thm]
) >>
FULL_SIMP_TAC std_ss [weak_trs_triple_def] 
);





(* Corollaries *)

val weak_trs_branch_corollary_thm = prove(``
(rel_is_weak_trs rel tr pc) ==>
(!ms. ((pc ms) IN (ls1 UNION ls2)) ==> (post1 ms) ==> (((pc ms) IN ls1) /\ (post ms))) ==>
(!ms. ((pc ms) IN (ls1 UNION ls2)) ==> (post2 ms) ==> (((pc ms) IN ls2) /\ (post ms))) ==>
(weak_trs_triple rel pc l (ls1 UNION ls2) (\ms. (pre ms) /\ (C1 ms)) post1) ==>
(weak_trs_triple rel pc l (ls1 UNION ls2) (\ms. (pre ms) /\ (~(C1 ms))) post2) ==>
(weak_trs_triple rel pc l (ls1 UNION ls2) pre post)
``,
REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc` , `l`, `(ls1 UNION ls2)`, `(\ms. (pre ms) /\ (C1 ms))`, `(\ms. (pre ms) /\ (C1 ms))`,
           `post1`, `post`]
           weak_trs_weak_rule_thm) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc` , `l`, `(ls1 UNION ls2)`, `(\ms. (pre ms) /\ (~(C1 ms)))`, `(\ms. (pre ms) /\ (~(C1 ms)))`,
           `post2`, `post`]
           weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
METIS_TAC [weak_trs_case_rule_thm]
);


(*

val weak_trs_seq_corollary_thm = prove(``
 ∀rel pc.
(rel_is_weak_trs rel tr pc) ==>
(~(l1 IN ls1)) ==>
(ls2 SUBSET ls1) ==>
(ls3 SUBSET ls1) ==>
(!ms. ((pc ms) IN ({l1} UNION ls1)) ==> (post1 ms) ==> (((pc ms) = l1) /\ (pre2 ms))) ==>
(!ms. ((pc ms) IN (ls2 UNION ls3)) ==> (post ms) ==> (((pc ms) IN ls2))) ==>
(weak_trs_triple rel pc l ({l1} UNION ls1) pre1 post1) ==>
(weak_trs_triple rel pc l1 (ls2 UNION ls3) pre2 post) ==>
(weak_trs_triple rel pc l (ls2 UNION ls3) pre1 post)
``,
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `({l1} UNION ls1) = (({l1} UNION (ls2 UNION ls3)) UNION ls1)` ASSUME_TAC >-
( cheat ) >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(∀l ms. (l ∈ ls1) ⇒ ¬((λl. if l ∈ {l1} then pre2 else (λms. F)) l ms))` ASSUME_TAC >-
(reo
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [pred_setTheory.IN_SING] >>
  (Cases_on `l' = l1`) >>
  (FULL_SIMP_TAC std_ss [])
) >>
ASSUME_TAC (Q.SPECL [`rel`,
           `pc`, `l`, `{l1} ∪ (ls2 ∪ ls3)`, `ls1`, `pre1`, `(λl. if l ∈ {l1} then pre2 else (λms. F))`]
           weak_trs_subset_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.SUBGOAL_THEN `(∀la ms.
 (la IN ({l1} ∪ (ls2 ∪ ls3))) ==>
 (((λl. if l ∈ {l1} then pre2 else (λms. F))) la ms) ⇒
 ((λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F)) la ms))` ASSUME_TAC >-
 (
 (METIS_TAC [pred_setTheory.IN_SING])
 ) >>
ASSUME_TAC (Q.SPECL [`rel`,
           `pc`, `l`, `{l1} ∪ (ls2 ∪ ls3)`, `pre1`, `pre1`,
           `(λl. if l ∈ {l1} then pre2 else (λms. F))`,
           `(λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F))`]
           weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.SUBGOAL_THEN `(∀la ms.
 (la IN (ls2 ∪ ls3)) ==>
 (((λl. if l ∈ ls2 then (post l) else (λms. F))) la ms) ⇒
 ((λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F)) la ms))` ASSUME_TAC >-
 (
 METIS_TAC [pred_setTheory.IN_SING, pred_setTheory.IN_UNION, pred_setTheory.SUBSET_DEF]
 ) >>
ASSUME_TAC (Q.SPECL [`rel`,
           `pc`, `l1`, `(ls2 ∪ ls3)`, `pre2`, `pre2`,
           `(λl. if l ∈ ls2 then (post l) else (λms. F))`,
           `(λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F))`]
           weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>


ASSUME_TAC (Q.SPECL [`rel`, `tr`,
           `pc`, `l`, `l1`, `(ls2 ∪ ls3)`, `pre1`, 
           `(λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F))`]
           weak_trs_seq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [pred_setTheory.IN_SING] >>

Q.SUBGOAL_THEN `(∀la ms.
 (la IN (ls2 ∪ ls3)) ==>
 (((λl'.
                if l' = l1 then pre2
                else if l' ∈ ls2 then post l'
                else (λms. F))) la ms) ⇒
 ((λl. if l ∈ ls2 then post l else (λms. F)) la ms))` ASSUME_TAC >-
 (
 METIS_TAC [pred_setTheory.IN_SING, pred_setTheory.IN_UNION, pred_setTheory.SUBSET_DEF]
 ) >>
ASSUME_TAC (Q.SPECL [`rel`,
           `pc`, `l`, `(ls2 ∪ ls3)`, `pre1`, `pre1`,
           `(λl. if (l IN {l1}) then pre2 else if l ∈ ls2 then post l else (λms. F))`,
           `(λl. if l ∈ ls2 then post l else (λms. F))`]
           weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [pred_setTheory.IN_SING]
);




*)



val _ = export_theory();



