open HolKernel Parse boolLib bossLib;
open bin_hoare_logicTheory;
open bir_auxiliaryTheory;

open bir_auxiliaryLib;

val _ = new_theory "bin_simp_hoare_logic";

(* Inv is usually the fact that the program is in memory and that
 * the execution mode is the expected one *)
val weak_map_triple_def = Define `
  weak_map_triple m invariant (l:'a) (ls:'a->bool) (ls':'a->bool) pre post =
    (((ls INTER ls') = EMPTY) /\
     (weak_triple m l (ls UNION ls')
                 (\ms. (pre ms) /\ (invariant ms))
                 (\ms. if ((m.pc ms) IN ls') then F else ((post ms) /\ (invariant ms)))
     )
    )
`;

val weak_map_subset_blacklist_rule_thm = prove(``
  !m.
  !invariant. !l ls ls' ls'' pre post.
  weak_model m ==>
  ls'' SUBSET ls' ==>
  weak_map_triple m invariant l ls ls' pre post ==>
  weak_map_triple m invariant l ls ls'' pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``, ``ls:'b->bool``] INTER_SUBSET_EMPTY_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``] SUBSET_EQ_UNION_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `!ms.
                ((\ms. m.pc ms NOTIN ls'' UNION v /\ post ms /\ invariant ms)) ms ==>
                m.pc ms NOTIN v` ASSUME_TAC >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] 
) >>
Q.SUBGOAL_THEN `(ls UNION (ls'' UNION v)) = ((ls UNION ls'') UNION v)`
  (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls''`, `v`,
	   `\ms:'a. pre ms /\ invariant ms`,
	   `\ms:'a. m.pc ms NOTIN (ls'':'b->bool) UNION v /\ post ms /\ invariant ms`] 
  weak_subset_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `!ms. ((m.pc ms) IN (ls UNION ls'')) ==>
                ((\ms. m.pc ms NOTIN ls'' UNION v /\ post ms /\ invariant ms) ms) ==>
                ((\ms. m.pc ms NOTIN ls'' /\ post ms /\ invariant ms) ms)` ASSUME_TAC >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls''`,
           `(\ms. pre ms /\ invariant ms)`, `(\ms. pre ms /\ invariant ms)`,
           `(\ms:'a. m.pc ms NOTIN (ls'':'b->bool) UNION v /\ post ms /\ invariant ms)`,
           `(\ms:'a. m.pc ms NOTIN (ls'':'b->bool) /\ post ms /\ invariant ms)`
           ] 
  weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_map_move_to_blacklist = store_thm("weak_map_move_to_blacklist",
  ``!m invariant l l' ls ls' pre post.
    weak_model m ==>
    l' IN ls ==>
    (!ms. (m.pc ms = l') ==> (post ms = F)) ==>
    weak_map_triple m invariant l ls ls' pre post ==>
    weak_map_triple m invariant l (ls DELETE l') (l' INSERT ls') pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def, weak_triple_def] >>
subgoal `?ls''. (ls = l' INSERT ls'') /\ l' NOTIN ls''` >- (
  METIS_TAC [pred_setTheory.DECOMPOSITION]
) >>
subgoal `l' NOTIN ls'` >- (
  METIS_TAC [pred_setTheory.INSERT_INTER, pred_setTheory.NOT_INSERT_EMPTY]
) >>
REPEAT STRIP_TAC >| [
  FULL_SIMP_TAC std_ss [pred_setTheory.DELETE_INTER, pred_setTheory.INSERT_INTER,
                        pred_setTheory.COMPONENT] >>
  ONCE_REWRITE_TAC [pred_setTheory.INTER_COMM] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INSERT_INTER,
                                                   pred_setTheory.COMPONENT,
                                                   pred_setTheory.INSERT_EQ_SING] >>
  `ls'' SUBSET ls` suffices_by (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INTER_COMM]
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [],

  QSPECL_X_ASSUM ``!ms. (m.pc ms = l) ==> _`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!ms. _`` [`ms'`] >>
  Q.EXISTS_TAC `ms'` >>
  subgoal `m.pc ms' <> l'` >- (
    CCONTR_TAC >>
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  `((l' INSERT ls'') DELETE l' UNION (l' INSERT ls')) = ((l' INSERT ls'') UNION ls')` suffices_by (
    FULL_SIMP_TAC std_ss []
  ) >>
  METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ,
             pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT]
]
);

val weak_map_move_set_to_blacklist = store_thm("weak_map_move_set_to_blacklist",
  ``!m invariant l ls ls' ls'' pre post.
    weak_model m ==>
    FINITE ls'' ==>
    ls'' SUBSET ls ==>
    (!ms l'.
     (l' IN ls'') ==>
     (m.pc ms = l') ==>
     (post ms = F)
    ) ==>
    weak_map_triple m invariant l ls ls' pre post ==>
    weak_map_triple m invariant l (ls DIFF ls'') (ls' UNION ls'') pre post``,

REPEAT STRIP_TAC >>
Induct_on `ls''` >>
REPEAT STRIP_TAC >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
subgoal `ls'' SUBSET ls` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
ASSUME_TAC
  (Q.SPECL [`m`, `invariant`, `l`, `e`, `(ls DIFF ls'')`,
            `(ls' UNION ls'')`, `pre`, `post`] weak_map_move_to_blacklist) >>
REV_FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
subgoal `ls DIFF (e INSERT ls'') = (ls DIFF ls'' DELETE e)` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.DIFF_INSERT] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.DELETE_DEF, pred_setTheory.DIFF_COMM]
) >>
subgoal `(ls' UNION (e INSERT ls'')) = (e INSERT ls' UNION ls'')` >- (
  ONCE_REWRITE_TAC [pred_setTheory.INSERT_SING_UNION] >>
  METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.UNION_ASSOC]
) >>
FULL_SIMP_TAC std_ss []
);

val weak_map_weakening_rule_thm = store_thm("weak_map_weakening_rule_thm",
  ``!m invariant l ls ls' pre post1 post2.
    weak_model m ==>
    (!ms. (m.pc ms) IN ls ==> (post1 ms) ==> (post2 ms)) ==>
    weak_map_triple m invariant l ls ls' pre post1 ==>
    weak_map_triple m invariant l ls ls' pre post2``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
subgoal `!ms. m.pc ms IN (ls UNION ls') ==>
         (\ms. m.pc ms NOTIN ls' /\ post1 ms /\ invariant ms) ms ==>
         (\ms. m.pc ms NOTIN ls' /\ post2 ms /\ invariant ms) ms` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls'`, `\ms. pre ms /\ invariant ms`, 
                     `\ms. pre ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN (ls':'b->bool) /\ post1 ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN (ls':'b->bool) /\ post2 ms /\ invariant ms`]
  weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);

val weak_map_strengthening_rule_thm = store_thm("weak_map_strengthening_rule_thm",
  ``!m invariant l ls ls' pre1 pre2 post.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    weak_map_triple m invariant l ls ls' pre1 post ==>
    weak_map_triple m invariant l ls ls' pre2 post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
subgoal `!ms. (m.pc ms = l) ==>
         (\ms. pre2 ms /\ invariant ms) ms ==>
         (\ms. pre1 ms /\ invariant ms) ms` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls UNION ls'`, `\ms. pre1 ms /\ invariant ms`, 
                     `\ms. pre2 ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN (ls':'b->bool) /\ post ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN (ls':'b->bool) /\ post ms /\ invariant ms`]
  weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_map_add_post_corollary_thm = prove(``
  !m invariant l ls ls' pre post1 post2.
  weak_model m ==>
  weak_map_triple m invariant l ls ls' pre post1 ==>
  weak_map_triple m invariant l ls ls' pre (\ms. if m.pc ms IN ls then post1 ms else post2 ms)``,

REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls`, `ls'`, `pre`,  `post1`, 
                     `(\ms. if m.pc ms IN ls then post1 ms else post2 ms)`]
  weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_map_add_post2_corollary = prove(``
  !m invariant l ls1 ls2 ls' pre post1 post2.
  weak_model m ==>
  ((ls1 INTER ls2) = EMPTY) ==>
  weak_map_triple m invariant l ls1 ls' pre post1 ==>
  weak_map_triple m invariant l ls1 ls' pre (\ms. if (m.pc ms IN ls2) then post2 ms else post1 ms)``,

REPEAT STRIP_TAC >>
subgoal `!ms. m.pc ms IN ls1 ==> post1 ms ==>
         (\ms. if m.pc ms IN ls2 then post2 ms else post1 ms) ms` >- (
  REPEAT STRIP_TAC >>
  METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
) >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls'`, `pre`,  `post1`,
                     `\ms. if m.pc ms IN ls2 then post2 ms else post1 ms`]
  weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] 
);


(* This proof should use the blacklist move lemma *)
val weak_map_seq_thm = prove(
  ``!m invariant l ls1 ls ls' pre post.
    weak_model m ==>
    (ls INTER ls' = {}) ==>
    weak_map_triple m invariant l ls1 (ls UNION ls') pre post ==>
    (!l1.
     (l1 IN ls1) ==>
     weak_map_triple m invariant l1 ls ls' post post
    ) ==>
    (weak_map_triple m invariant l ls ls' pre post)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Massage first contract *)
subgoal `(!ms. m.pc ms IN (ls1 UNION (ls UNION ls')) ==>
         (\ms. m.pc ms NOTIN ls UNION ls' /\ post ms /\ invariant ms) ms ==>
         (\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms) ms)` >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`m`, `l`, `ls1 UNION (ls UNION ls')`, `\ms. pre ms /\ invariant ms`,
                     `\ms. pre ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN ls UNION ls' /\ post ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`]
  weak_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Massage the second contract *)
subgoal `!l1. l1 IN ls1 ==>
         weak_triple m l1 (ls UNION ls') (\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms)
         (\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms)` >- (
  REPEAT STRIP_TAC >>
  subgoal `!ms.
           (m.pc ms = l1) ==>
           (\ms. post ms /\ invariant ms) ms ==>
           (\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms) ms` >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss)
      [pred_setTheory.UNION_OVER_INTER] >>
    METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
  ) >>
  ASSUME_TAC (Q.SPECL [`m`, `l1`, `ls UNION ls'`,
                       `\ms. post ms /\ invariant ms`,
                       `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`,
                       `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`,
                       `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`]
    weak_weakening_rule_thm) >>
  REV_FULL_SIMP_TAC std_ss []
) >>

ASSUME_TAC (Q.SPECL [`m`, `l`, `ls1`, `ls UNION ls'`,
                     `\ms. pre ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`]
  weak_seq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


(* We should generalize the other contract to handle set of labels *)
val weak_map_std_seq_comp_thm = store_thm("weak_map_std_seq_comp_thm",
  ``!m ls1 ls1' ls2 ls2' invariant l pre1 post1 post2.
    weak_model m ==>
    ls1' SUBSET ls2 ==>
    (ls1 INTER ls1' = EMPTY) ==>
    (ls1' INTER ls2' = EMPTY) ==>
    weak_map_triple m invariant l ls1 ls2 pre1 post1 ==>
    (!l1. (l1 IN ls1) ==> (weak_map_triple m invariant l1 ls1' ls2' post1 post2)) ==>
    weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1 post2``,

REPEAT STRIP_TAC >>
(* First we extend the initial contract to have the same postcondition *)
subgoal `weak_map_triple m invariant l ls1 ls2 pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  METIS_TAC [weak_map_add_post_corollary_thm]
) >>
(* We then restrict the non-accessible addresses of the first contract *)
subgoal `ls1' UNION (ls2 INTER ls2') SUBSET ls2` >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
) >>
subgoal `weak_map_triple m invariant l ls1 (ls1' UNION ls2 INTER ls2') pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  METIS_TAC [weak_map_subset_blacklist_rule_thm]
) >>
(* Now, we extend the second contracts *)
subgoal `!l1.
         l1 IN ls1 ==>
         weak_map_triple m invariant l1 ls1' (ls2 INTER ls2')
           ((\ms. if m.pc ms IN ls1 then post1 ms else post2 ms))
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>  
  REV_FULL_SIMP_TAC std_ss [] >>
  (* Now, we extend the second contract to have the same postcondition *)
  subgoal `weak_map_triple m invariant l1 ls1' ls2' post1
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
    METIS_TAC [weak_map_add_post2_corollary, pred_setTheory.INTER_COMM]
  ) >>
  (* We then restrict the non-accessible addresses of the first contract *)
  subgoal `weak_map_triple m invariant l1 ls1' (ls2 INTER ls2') post1
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
    METIS_TAC [weak_map_subset_blacklist_rule_thm, pred_setTheory.INTER_SUBSET]
  ) >>
  FULL_SIMP_TAC std_ss [weak_triple_def, weak_map_triple_def]
) >>
subgoal `weak_map_triple m invariant l ls1' (ls2 INTER ls2') pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls1'`, `(ls2 INTER ls2')`,
                       `pre1`, `(\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)`]
    weak_map_seq_thm
  ) >>
  METIS_TAC [INTER_EMPTY_INTER_INTER_EMPTY_thm, pred_setTheory.INTER_COMM]
) >>
subgoal `(!ms. m.pc ms IN ls1' ==>
	  (\ms.
	   if m.pc ms IN ls1
	   then post1 ms
	   else post2 ms) ms ==>
	   post2 ms)` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  subgoal `~(m.pc ms IN ls1)` >- (
    METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] 
) >>
(* Finish everything... *)
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1'`, `ls2 INTER ls2'`, `pre1`,
                     `(\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)`,
                     `post2`]
  weak_map_weakening_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val weak_map_loop_thm = store_thm("weak_map_loop_thm",
  ``!m.
    weak_model m ==>
    !l wl bl invariant C1 var post.
    l NOTIN wl ==> 
    l NOTIN bl ==>
    (wl INTER bl = EMPTY) ==>
    (!x. weak_map_triple m invariant l ({l} UNION wl) bl
      (\ms. C1 ms /\ (var ms = (x:num)))
      (\ms. (m.pc ms = l) /\ var ms < x /\ var ms >= 0)) ==>
    weak_map_triple m invariant l wl bl (\ms. ~(C1 ms)) post ==>
    weak_map_triple m invariant l wl bl (\ms. T) post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
irule weak_invariant_rule_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `C1` >>
Q.EXISTS_TAC `var` >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
  [weak_loop_contract_def, Once boolTheory.CONJ_SYM] >>
STRIP_TAC >>
QSPECL_X_ASSUM ``!x. _`` [`x`] >>  
irule weak_weakening_rule_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `(\ms.
                m.pc ms NOTIN bl /\ ((m.pc ms = l) /\ var ms < x) /\
                invariant ms)` >>
Q.EXISTS_TAC `(\ms. (C1 ms /\ (var ms = x)) /\ invariant ms)` >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.UNION_ASSOC]
);

(* The below are still TODO: *)
(*
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
*)

val _ = export_theory();



