open HolKernel Parse boolLib bossLib;
open bin_hoare_logicTheory;

open bir_auxiliaryLib;

val _ = new_theory "bin_simp_hoare_logic";

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

val INTER_EMPTY_IN_NOT_IN_thm = prove(``
!x y z. (x INTER y = EMPTY) ==> (z IN x) ==> (~(z IN y))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.INTER_DEF] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.EMPTY_DEF] >>
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
  QSPECL_X_ASSUM ``!x.P`` [`z`] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC []
);

val INTER_EMPTY_INTER_INTER_EMPTY_thm = prove(``
!x y z. (x INTER y = EMPTY) ==> (x INTER (y INTER z) = EMPTY)
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC (std_ss) [Once pred_setTheory.INTER_ASSOC] >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
);



(* Inv is usually the fact that the program is in memory and that
the execution mode is the exprected one *)
val weak_map_triple_def = Define `
  weak_map_triple m invariant (l:'a) (ls:'a->bool) (ls':'a->bool) pre post =
  (((ls INTER ls') = EMPTY) /\
  (weak_triple m l (ls UNION ls') (\ms. (pre ms) /\ (invariant ms)) (\ms. if ((m.pc ms) IN ls') then F else ((post (m.pc ms) ms) /\ (invariant ms)))))
`;

val weak_map_subset_blacklist_rule_thm = prove(``
! m.
!invariant . ! l ls ls' ls'' pre post.
(weak_model m) ==>
(ls'' SUBSET ls') ==>
(weak_map_triple m invariant l ls ls' pre post) ==>
(weak_map_triple m invariant l ls ls'' pre post)
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``, ``ls:'b->bool``] INTER_SUBSET_EMPTY_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``] SUBSET_EQ_UNION_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(∀ms. ((λms. m.pc ms ∉ ls'' ∪ v ∧ post (m.pc ms) ms ∧ invariant ms)) ms ⇒ m.pc ms ∉ v)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
) >>

Q.SUBGOAL_THEN `(ls UNION (ls'' UNION v)) = ((ls UNION ls'') UNION v)` (fn thm => FULL_SIMP_TAC std_ss [thm]) >-
  (FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls''`, `v`,
           `(λms:'a. pre ms ∧ invariant ms)`,
           `(λms:'a. m.pc ms ∉ (ls'':'b->bool) ∪ v ∧ post (m.pc ms) ms ∧ invariant ms)`] 
  weak_subset_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `(!ms. ((m.pc ms) IN (ls UNION ls'')) ==>
               ((λms. m.pc ms ∉ ls'' ∪ v ∧ post (m.pc ms) ms ∧ invariant ms) ms) ==> ((λms. m.pc ms ∉ ls'' ∧ post (m.pc ms) ms ∧ invariant ms) ms))` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls''`,
           `(λms. pre ms ∧ invariant ms)`, `(λms. pre ms ∧ invariant ms)`,
           `(λms:'a. m.pc ms ∉ (ls'':'b->bool) ∪ v ∧ post (m.pc ms) ms ∧ invariant ms)`,
           `(λms:'a. m.pc ms ∉ (ls'':'b->bool) ∧ post (m.pc ms) ms ∧ invariant ms)`
           ] 
  weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


(* TODO 
val weak_simp_trs_blacklist_move_thm = prove(``
! rel tr pc l ls ls' ls'' pre post.
(rel_is_weak_trs rel tr pc) ==>
(ls' INTER ls'' = EMPTY) ==>
(weak_simp_trs_triple rel pc invariant l ls (ls' UNION ls'') pre post) ==>
(weak_simp_trs_triple rel pc invariant l (ls UNION ls') ls'' pre post)
``
*)

val weak_map_weakening_rule_thm = prove(``
! m invariant l ls ls' pre post1 post2.
(weak_model m) ==>
(!ms. (m.pc ms) IN ls ==> (post1 (m.pc ms) ms) ==> (post2 (m.pc ms) ms)) ==>
(weak_map_triple m invariant l ls ls' pre post1) ==>
(weak_map_triple m invariant l ls ls' pre post2)
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
Q.SUBGOAL_THEN `∀ms. m.pc ms ∈ (ls ∪ ls') ⇒ (λms. m.pc ms ∉ ls' ∧ post1 (m.pc ms) ms ∧ invariant ms) ms ⇒
               (λms. m.pc ms ∉ ls' ∧ post2 (m.pc ms) ms ∧ invariant ms) ms` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls'`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. m.pc ms ∉ (ls':'b->bool) ∧ post1 (m.pc ms) ms ∧ invariant ms)`,
  `(λms. m.pc ms ∉ (ls':'b->bool) ∧ post2 (m.pc ms) ms ∧ invariant ms)`]
 weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);



val weak_map_add_post_corollary_thm = prove(``
! m invariant l ls ls' pre post1 post2.
(weak_model m) ==>
(weak_map_triple m invariant l ls ls' pre post1) ==>
(weak_map_triple m invariant l ls ls' pre (\l ms. if l IN ls then post1 l ms else post2 l ms))
``,

REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls`, `ls'`, `pre`,  `post1`,  `(\l ms. if l IN ls then post1 l ms else post2 l ms)`]
 weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_map_add_post2_corollary = prove(``
! m invariant l ls1 ls2 ls' pre post1 post2.
(weak_model m) ==>
((ls1 INTER ls2) = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls' pre post1) ==>
(weak_map_triple m invariant l ls1 ls' pre (\l ms. if (l IN ls2) then post2 l ms else post1 l ms))
``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `(∀ms. m.pc ms ∈ ls1 ⇒ post1 (m.pc ms) ms ⇒
              (λl ms. if l ∈ ls2 then post2 l ms else post1 l ms) (m.pc ms) ms)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
) >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls'`, `pre`,  `post1`,  `(\l ms. if l IN ls2 then post2 l ms else post1 l ms)`]
 weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] 
);





(* This prove should use the blacklist move lemma *)
val weak_map_seq_thm = prove(
  ``!m invariant l ls1 ls ls' pre post.
    weak_model m ==>
    (ls ∩ ls' = ∅) ==>
    weak_map_triple m invariant l ls1 (ls UNION ls') pre post ==>
    (!l1.
     (l1 IN ls1) ==>
     weak_map_triple m invariant l1 ls ls' (post l1) post
    ) ==>
    (weak_map_triple m invariant l ls ls' pre post)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Massage first contract *)
Q.SUBGOAL_THEN `(∀ms. m.pc ms ∈ (ls1 ∪ (ls ∪ ls')) ⇒
               (λms. m.pc ms ∉ ls ∪ ls' ∧ post (m.pc ms) ms ∧ invariant ms) ms ⇒
               (λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms) ms)` ASSUME_TAC >-
(
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls1 UNION (ls UNION ls')`, `(λms. pre ms ∧ invariant ms)`,  `(λms. pre ms ∧ invariant ms)`,
  `(λms. m.pc ms ∉ ls ∪ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`,
  `(λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`]
 weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

(* Massage the second contracts *)
Q.SUBGOAL_THEN `∀l1. l1 ∈ ls1 ⇒
               weak_triple m l1 (ls ∪ ls') (λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)
               (λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!l1:'b. (l1 IN ls1) ==> P`` [`l1`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.SUBGOAL_THEN `∀ms. (m.pc ms = l1) ⇒
  (λms. post l1 ms ∧ invariant ms) ms ⇒
  (λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms) ms
  ` ASSUME_TAC >-
  (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.UNION_OVER_INTER] >>
    METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
  ) >>
  ASSUME_TAC (Q.SPECL [`m`, `l1`, `ls UNION ls'`,
    `(λms. post l1 ms ∧ invariant ms)`,  `(λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`,
    `(λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`,
    `(λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`]
   weak_weakening_rule_thm) >>
  REV_FULL_SIMP_TAC std_ss []
) >>

ASSUME_TAC (Q.SPECL [`m`, `l`, `ls1`, `ls UNION ls'`,
 `(λms. pre ms ∧ invariant ms)`, `(λms. m.pc ms ∉ ls' ∧ post (m.pc ms) ms ∧ invariant ms)`]
  weak_seq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);







(* We should generalize the other contact to handle set of labels *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,

REPEAT STRIP_TAC >>

(* First we extend the initial contract to have the same postcondition *)
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls2`, `pre1`, `post1`, `post2`]
           weak_map_add_post_corollary_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* We then restrict the non-accessible addresses of the first contract *)
Q.SUBGOAL_THEN `ls1' UNION (ls2 ∩ ls2') SUBSET ls2` ASSUME_TAC >-
(
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls2`, `ls1' UNION (ls2 INTER ls2')`, `pre1`,
           `(λl ms. if l ∈ ls1 then post1 l ms else post2 l ms)`]
           weak_map_subset_blacklist_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>

(* Now, we extend the second contracts *)
Q.SUBGOAL_THEN `∀l1.
             l1 ∈ ls1 ⇒
             weak_map_triple m invariant l1 ls1' (ls2 INTER ls2') ((λl ms. if l ∈ ls1 then post1 l ms else post2 l ms) l1)
             (λl ms. if l ∈ ls1 then post1 l ms else post2 l ms)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!x.P`` [`l1`] >>  
  REV_FULL_SIMP_TAC std_ss [] >>
  (* Now, we extend the second contract to have the same postcondition *)
  ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l1`, `ls1'`, `ls1`, `ls2'`, `post1 l1`, `post2`, `post1`]
           weak_map_add_post2_corollary) >>
  REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
  (* We then restrict the non-accessible addresses of the first contract *)
  Q.SUBGOAL_THEN `(ls2 ∩ ls2') SUBSET ls2'` ASSUME_TAC >-
  (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
  ) >>
  ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l1`, `ls1'`, `ls2'`, `ls2 INTER ls2'`, `post1 l1`,
           `(λl ms. if l ∈ ls1 then post1 l ms else post2 l ms)`]
           weak_map_subset_blacklist_rule_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.SUBGOAL_THEN `(λms. post1 l1 ms) = (post1 l1)` (FULLSIMP_BY_THM std_ss) >- (METIS_TAC [])
) >>


ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls1'`, `(ls2 INTER ls2')`, `pre1`, `(λl ms. if l ∈ ls1 then post1 l ms else post2 l ms)`]
  weak_map_seq_thm) >>
REV_FULL_SIMP_TAC  (std_ss) [] >>
Q.SUBGOAL_THEN `(ls1' ∩ (ls2 ∩ ls2') = ∅)` (FULLSIMP_BY_THM std_ss) >-
(
   FULL_SIMP_TAC  (std_ss) [INTER_EMPTY_INTER_INTER_EMPTY_thm] >>
   cheat
) >>

Q.SUBGOAL_THEN `(∀ms. m.pc ms ∈ ls1' ⇒ (λl' ms. if l' IN ls1 then post1 (m.pc ms) ms else post2 l' ms) (m.pc ms) ms ⇒ post2 (m.pc ms) ms)` ASSUME_TAC >-
(
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  cheat >>
  Q.SUBGOAL_THEN `(pc ms) <> l1` (FULLSIMP_BY_THM std_ss) >>
  FULL_SIMP_TAC std_ss [] 
) >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1'`, `ls2 INTER ls2'`, `pre1`,
           `(λl' ms. if l' IN ls1 then post1 l' ms else post2 l' ms)`, `post2`]
   weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);



(* Condition *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,

cheat);


(* loop *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,cheat);


(* Function call *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,

cheat);


(* Recursive function *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,

cheat);


(* Mutually Recursive function *)
val weak_map_std_seq_comp_thm = prove(``
(weak_model m) ==>
(ls1' SUBSET ls2) ==>
(ls1 INTER ls1' = EMPTY) ==>
(ls1' INTER ls2' = EMPTY) ==>
(weak_map_triple m invariant l ls1 ls2 pre1 post1) ==>
(!l1 . (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' (post1 l1) post2)) ==>
(weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2)
``,

cheat);


val _ = export_theory();



