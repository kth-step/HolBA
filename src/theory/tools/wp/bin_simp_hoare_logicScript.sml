open HolKernel Parse boolLib bossLib;
open bin_hoare_logicTheory;

val _ = new_theory "bin_hoare_logic";

val INTER_SUBSET_EMPTY_thm = prove(``!s t v.
(s SUBSET t) ==> (v INTER t = EMPTY) ==> (v INTER s = EMPTY)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.INTER_DEF, pred_setTheory.EMPTY_DEF, FUN_EQ_THM]  >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >>
METIS_TAC []
);

val SUBSET_EQ_UNION_thm = prove(``!s t.
(s SUBSET t) ==> (? v. t = s UNION v)
``,
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `t` >>
METIS_TAC [pred_setTheory.SUBSET_UNION_ABSORPTION]
);

val IN_NOT_IN_NEQ_thm = prove(``
!x y z.
(x IN z) ==> (~(y IN z)) ==> (x <> y)
``,
 FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
);

val SING_DISJOINT_SING_NOT_IN_thm = prove(``
!x y. ((x INTER {y}) = EMPTY) ==>(~(y IN x))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.INTER_DEF] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.EMPTY_DEF] >>
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
  QSPECL_X_ASSUM ``!x.P`` [`y`] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
);

(* Inv is usually the fact that the program is in memory and that
the execution mode is the exprected one *)
val weak_simp_trs_triple_def = Define `
  weak_simp_trs_triple rel pc invariant (l:'a) (ls:'a->bool) (ls':'a->bool) pre post =
  (((ls INTER ls') = EMPTY) /\
  (weak_trs_triple rel pc l (ls UNION ls') (\ms. (pre ms) /\ (invariant ms)) (\ms. if ((pc ms) IN ls') then F else ((post (pc ms) ms) /\ (invariant ms)))))
`;

val weak_simp_trs_subset_blacklist_thm = prove(``
! rel tr pc l ls ls' ls'' pre post.
(rel_is_weak_trs rel tr pc) ==>
(ls'' SUBSET ls') ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post) ==>
(weak_simp_trs_triple rel pc invariant l ls ls'' pre post)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``, ``ls:'b->bool``] INTER_SUBSET_EMPTY_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``] SUBSET_EQ_UNION_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(∀ms. ((λms. pc ms ∉ ls'' ∪ v ∧ post (pc ms) ms ∧ invariant ms)) ms ⇒ pc ms ∉ v)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
) >>

Q.SUBGOAL_THEN `(ls UNION (ls'' UNION v)) = ((ls UNION ls'') UNION v)` (fn thm => FULL_SIMP_TAC std_ss [thm]) >-
  (FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls UNION ls''`, `v`,
           `(λms:'a. pre ms ∧ invariant ms)`,
           `(λms:'a. pc ms ∉ (ls'':'b->bool) ∪ v ∧ post (pc ms) ms ∧ invariant ms)`] 
  weak_trs_subset_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(!ms. ((pc ms) IN (ls UNION ls'')) ==>
               ((λms. pc ms ∉ ls'' ∪ v ∧ post (pc ms) ms ∧ invariant ms) ms) ==> ((λms. pc ms ∉ ls'' ∧ post (pc ms) ms ∧ invariant ms) ms))` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls UNION ls''`,
           `(λms. pre ms ∧ invariant ms)`, `(λms. pre ms ∧ invariant ms)`,
           `(λms:'a. pc ms ∉ (ls'':'b->bool) ∪ v ∧ post (pc ms) ms ∧ invariant ms)`,
           `(λms:'a. pc ms ∉ (ls'':'b->bool) ∧ post (pc ms) ms ∧ invariant ms)`
           ] 
  weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


(* TODO 
val weak_simp_trs_blacklist_move_thm = prove(``
! rel tr pc l ls ls' ls'' pre post.
(rel_is_weak_trs rel tr pc) ==>
(ls' INTER ls'' = EMPTY) ==>
(weak_simp_trs_triple rel pc invariant l ls (ls' UNION ls'') pre post) ==>
(weak_simp_trs_triple rel pc invariant l (ls UNION ls') ls'' pre post)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
Q.SUBGOAL_THEN `(ls UNION (ls' UNION ls'')) = ((ls UNION ls') UNION ls'')` (fn thm => FULL_SIMP_TAC std_ss [thm]) >-
  (FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []) >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``, ``ls:'b->bool``] INTER_SUBSET_EMPTY_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``] SUBSET_EQ_UNION_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(∀ms. ((λms. pc ms ∉ ls'' ∪ v ∧ post (pc ms) ms ∧ invariant ms)) ms ⇒ pc ms ∉ v)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
) >>
);
*)

val weak_simp_trs_weak_rule_thm = prove(``
! rel tr pc l ls ls' pre post1 post2.
(rel_is_weak_trs rel tr pc) ==>
(!ms. (pc ms) IN ls ==> (post1 (pc ms) ms) ==> (post2 (pc ms) ms)) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post1) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post2)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
Q.SUBGOAL_THEN `∀ms. pc ms ∈ (ls ∪ ls') ⇒ (λms. pc ms ∉ ls' ∧ post1 (pc ms) ms ∧ invariant ms) ms ⇒
               (λms. pc ms ∉ ls' ∧ post2 (pc ms) ms ∧ invariant ms) ms` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls UNION ls'`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. pc ms ∉ (ls':'b->bool) ∧ post1 (pc ms) ms ∧ invariant ms)`,
  `(λms. pc ms ∉ (ls':'b->bool) ∧ post2 (pc ms) ms ∧ invariant ms)`]
 weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);



val weak_simp_trs_add_post_thm = prove(``
! rel tr pc l ls ls' pre post1 post2.
(rel_is_weak_trs rel tr pc) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post1) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre (\l ms. if l IN ls then post1 l ms else post2 l ms))
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
Q.SUBGOAL_THEN `∀ms. pc ms ∈ (ls ∪ ls') ⇒ (λms. pc ms ∉ ls' ∧ post1 (pc ms) ms ∧ invariant ms) ms ⇒
               (λms.
          pc ms ∉ ls' ∧ (if (pc ms) ∈ ls then post1 (pc ms) ms else post2 (pc ms) ms) ∧
          invariant ms) ms` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls UNION ls'`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. pc ms ∉ (ls':'b->bool) ∧ post1 (pc ms) ms ∧ invariant ms)`,
  `(λms.
          pc ms ∉  (ls':'b->bool) ∧ (if (pc ms) ∈ (ls:'b->bool) then post1 (pc ms) ms else post2 (pc ms) ms) ∧
          invariant ms)`]
 weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_simp_trs_add_post2_thm = prove(``
! rel tr pc l l1 ls ls' pre post1 post2.
(rel_is_weak_trs rel tr pc) ==>
~((l1 IN ls)) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post1) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre (\l ms. if (l IN {l1}) then post2 l ms else post1 l ms))
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
Q.SUBGOAL_THEN `∀ms. pc ms ∈ (ls ∪ ls') ⇒ (λms. pc ms ∉ ls' ∧ post1 (pc ms) ms ∧ invariant ms) ms ⇒
               (λms.
          pc ms ∉ ls' ∧ (if (pc ms) ∈ {l1} then post2 (pc ms) ms else post1 (pc ms) ms) ∧
          invariant ms) ms` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC [IN_NOT_IN_NEQ_thm]
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls UNION ls'`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. pc ms ∉ (ls':'b->bool) ∧ post1 (pc ms) ms ∧ invariant ms)`,
  `(λms.
          pc ms ∉  (ls':'b->bool) ∧ (if (pc ms) ∈ {l1} then post2 (pc ms) ms else post1 (pc ms) ms) ∧
          invariant ms)`]
 weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


(* This prove should use the blacklist move lemma *)
val weak_simp_trs_seq_thm = prove(``
! rel tr pc l l1 ls ls' pre post.
(rel_is_weak_trs rel tr pc) ==>
(weak_simp_trs_triple rel pc invariant l {l1} (ls UNION ls') pre post) ==>
(weak_simp_trs_triple rel pc invariant l1 ls ls' (post l1) post) ==>
(weak_simp_trs_triple rel pc invariant l ls ls' pre post)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_simp_trs_triple_def] >>
Q.SUBGOAL_THEN `∀ms. (pc ms = l1) ⇒
(λms. post l1 ms ∧ invariant ms) ms ⇒
(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms) ms
` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.UNION_OVER_INTER] >>
  FULL_SIMP_TAC std_ss [SING_DISJOINT_SING_NOT_IN_thm]
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l1`, `ls UNION ls'`,
  `(λms. post l1 ms ∧ invariant ms)`,  `(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms)`,
  `(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms)`,
  `(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms)`]
 weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(∀ms. pc ms ∈ ({l1} ∪ (ls ∪ ls')) ⇒
               (λms. pc ms ∉ ls ∪ ls' ∧ post (pc ms) ms ∧ invariant ms) ms ⇒
               (λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms) ms)` ASSUME_TAC >-
(
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `{l1} UNION (ls UNION ls')`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. pc ms ∉ ls ∪ ls' ∧ post (pc ms) ms ∧ invariant ms)`,
  `(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms)`]
 weak_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `l1`, `ls UNION ls'`,
 `(λms. pre ms ∧ invariant ms)`, `(λms. pc ms ∉ ls' ∧ post (pc ms) ms ∧ invariant ms)`]
  weak_trs_seq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);








(* We chould generalize the other contact to handle set of labels *)
val weak_simp_trs_seq_comp_thm = prove(``
(rel_is_weak_trs rel tr pc) ==>
(ls1' SUBSET ls2) ==>
(~(l1 IN ls1')) ==>
(weak_simp_trs_triple rel pc invariant l {l1} ls2 pre1 post1) ==>
(weak_simp_trs_triple rel pc invariant l1 ls1' ls2' (post1 l1) post2) ==>
(weak_simp_trs_triple rel pc invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,
REPEAT STRIP_TAC >>

(* First we extend the fist contract to have the same postcondition *)
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `{l1}`, `ls2`, `pre1`, `post1`, `post2`]
           weak_simp_trs_add_post_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* We then restrict the non-accessible addresses of the first contract *)
Q.SUBGOAL_THEN `ls1' UNION (ls2 ∩ ls2') SUBSET ls2` ASSUME_TAC >-
(
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `{l1}`, `ls2`, `ls1' UNION (ls2 INTER ls2')`, `pre1`,
           `(λl ms. if l ∈ {l1} then post1 l ms else post2 l ms)`]
           weak_simp_trs_subset_blacklist_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

(* Now, we extend the second contract to have the same postcondition *)
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l1`, `l1`, `ls1'`, `ls2'`, `post1 l1`, `post2`, `post1`]
           weak_simp_trs_add_post2_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* We then restrict the non-accessible addresses of the first contract *)
Q.SUBGOAL_THEN `(ls2 ∩ ls2') SUBSET ls2'` ASSUME_TAC >-
(
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l1`, `ls1'`, `ls2'`, `ls2 INTER ls2'`, `post1 l1`,
           `(λl ms. if l ∈ {l1} then post1 l ms else post2 l ms)`]
           weak_simp_trs_subset_blacklist_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `l1`, `ls1'`, `(ls2 INTER ls2')`, `pre1`, `(λl ms. if l ∈ {l1} then post1 l ms else post2 l ms)`]
  weak_simp_trs_seq_thm) >>
REV_FULL_SIMP_TAC  (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
Q.SUBGOAL_THEN `(λms. post1 l1 ms) = (post1 l1)` (FULLSIMP_BY_THM std_ss) >- (METIS_TAC []) >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.SUBGOAL_THEN `(∀ms. pc ms ∈ ls1' ⇒ (λl' ms. if l' = l1 then post1 l1 ms else post2 l' ms) (pc ms) ms ⇒ post2 (pc ms) ms)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  Q.SUBGOAL_THEN `(pc ms) <> l1` (FULLSIMP_BY_THM std_ss) >>
  METIS_TAC [IN_NOT_IN_NEQ_thm]
) >>
ASSUME_TAC (Q.SPECL [`rel`, `tr`, `pc`, `l`, `ls1'`, `ls2 INTER ls2'`, `pre1`,
           `(λl' ms. if l' = l1 then post1 l1 ms else post2 l' ms)`, `post2`]
   weak_simp_trs_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);

val _ = export_theory();
