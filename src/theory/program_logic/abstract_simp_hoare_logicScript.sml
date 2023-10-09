open HolKernel Parse boolLib bossLib;
open abstract_hoare_logicTheory;
open bir_auxiliaryTheory;

open bir_auxiliaryLib;

val _ = new_theory "abstract_simp_hoare_logic";

(* Inv is usually the fact that the program is in memory and that
 * the execution mode is the expected one *)
val abstract_simp_jgmt_def = Define `
  abstract_simp_jgmt m invariant (l:'a) (ls:'a->bool) (ls':'a->bool) pre post =
    (((ls INTER ls') = EMPTY) /\ (ls <> EMPTY) /\
     (abstract_jgmt m l (ls UNION ls')
                 (\ms. (pre ms) /\ (invariant ms))
                 (\ms. if ((m.pc ms) IN ls') then F else ((post ms) /\ (invariant ms)))
     )
    )
`;


val abstract_simp_weak_model_comp_rule_thm =
  store_thm("abstract_simp_weak_model_comp_rule_thm",
  ``!m n invariant l ls ls' pre post.
    weak_model m ==>
    weak_model n ==>
    (!ms ls ms'. m.weak ms ls ms' ==> n.weak ms ls ms') ==>
    (!ms l. (n.pc ms = l)  ==> (m.pc ms = l)) ==>
    abstract_simp_jgmt m invariant l ls ls' pre post ==>
    abstract_simp_jgmt n invariant l ls ls' pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
irule abstract_weak_model_comp_rule_thm >>
METIS_TAC []
);


val abstract_simp_bl_subset_rule_thm =
  store_thm("abstract_simp_bl_subset_rule_thm",
  ``!m.
    !invariant. !l ls ls' ls'' pre post.
    weak_model m ==>
    ls'' SUBSET ls' ==>
    abstract_simp_jgmt m invariant l ls ls' pre post ==>
    abstract_simp_jgmt m invariant l ls ls'' pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
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
  abstract_subset_rule_thm) >>
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
  abstract_conseq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val abstract_simp_bl_to_wl_rule_thm = store_thm("abstract_simp_bl_to_wl_rule_thm",
  ``!m invariant l l' ls ls' pre post.
    weak_model m ==>
    l' IN ls' ==>
    abstract_simp_jgmt m invariant l ls ls' pre post ==>
    abstract_simp_jgmt m invariant l (l' INSERT ls) (ls' DELETE l') pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
subgoal `?ls''. (ls' = l' INSERT ls'') /\ l' NOTIN ls''` >- (
  METIS_TAC [pred_setTheory.DECOMPOSITION]
) >>
subgoal `l' NOTIN ls` >- (
  CCONTR_TAC >>
  subgoal `?ls'''. (ls = l' INSERT ls''') /\ l' NOTIN ls'''` >- (
    METIS_TAC [pred_setTheory.DECOMPOSITION]
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INSERT_INTER]
) >>
REPEAT STRIP_TAC >| [
  ONCE_REWRITE_TAC [pred_setTheory.INTER_COMM] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.DELETE_INTER, pred_setTheory.INSERT_INTER,
                        pred_setTheory.COMPONENT] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INSERT_INTER,
                                                   pred_setTheory.COMPONENT,
                                                   pred_setTheory.INSERT_EQ_SING] >>
  FULL_SIMP_TAC std_ss [Once pred_setTheory.INTER_COMM] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INSERT_INTER] >>
  FULL_SIMP_TAC std_ss [Once pred_setTheory.INTER_COMM],

  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [],

  irule abstract_conseq_rule_thm >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  Q.EXISTS_TAC `(\ms. m.pc ms NOTIN l' INSERT ls'' /\ post ms /\ invariant ms)` >>
  Q.EXISTS_TAC `(\ms. pre ms /\ invariant ms)` >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  `((l' INSERT ls) UNION ((l' INSERT ls'') DELETE l')) = (ls UNION (l' INSERT ls''))` suffices_by (
    FULL_SIMP_TAC std_ss []
  ) >>
  METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ,
             pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT]
]
);


val abstract_simp_wl_to_bl_rule_thm = store_thm("abstract_simp_wl_to_bl_rule_thm",
  ``!m invariant l l' ls ls' pre post.
    weak_model m ==>
    l' IN ls ==>
    (ls DELETE l') <> {} ==>
    (!ms. (m.pc ms = l') ==> (post ms = F)) ==>
    abstract_simp_jgmt m invariant l ls ls' pre post ==>
    abstract_simp_jgmt m invariant l (ls DELETE l') (l' INSERT ls') pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
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

  irule abstract_conseq_rule_thm >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms` >>
  Q.EXISTS_TAC `\ms. pre ms /\ invariant ms` >>
  FULL_SIMP_TAC std_ss [] >>
  REPEAT STRIP_TAC >- (
    QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
    Cases_on `m.pc ms = l'` >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
    )
  ) >>
  `(l' INSERT ls'') DELETE l' UNION (l' INSERT ls') = ((l' INSERT ls'') UNION ls')` suffices_by (
    FULL_SIMP_TAC std_ss []
  ) >>
  METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ,
             pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT]
]
);


val abstract_simp_wl_to_bl_set_rule_thm = store_thm("abstract_simp_wl_to_bl_set_rule_thm",
  ``!m invariant l ls ls' ls'' pre post.
    weak_model m ==>
    FINITE ls'' ==>
    ls'' PSUBSET ls ==>
    (!ms l'.
     (l' IN ls'') ==>
     (m.pc ms = l') ==>
     (post ms = F)
    ) ==>
    abstract_simp_jgmt m invariant l ls ls' pre post ==>
    abstract_simp_jgmt m invariant l (ls DIFF ls'') (ls' UNION ls'') pre post``,

REPEAT STRIP_TAC >>
Induct_on `ls''` >>
REPEAT STRIP_TAC >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
subgoal `ls'' PSUBSET ls` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.PSUBSET_DEF] >>
  METIS_TAC [pred_setTheory.NOT_EQUAL_SETS]
) >>
subgoal `e IN ls` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.PSUBSET_DEF]
) >>
subgoal `ls DIFF ls'' <> {e}` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.PSUBSET_MEMBER] >>
  subgoal `y IN ls DIFF ls''` >- (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.IN_DIFF]
  ) >>
  subgoal `y NOTIN {e}` >- (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.NOT_EQUAL_SETS] >>
  Q.EXISTS_TAC `y` >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
ASSUME_TAC
  (Q.SPECL [`m`, `invariant`, `l`, `e`, `(ls DIFF ls'')`,
            `(ls' UNION ls'')`, `pre`, `post`] abstract_simp_wl_to_bl_rule_thm) >>
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

val abstract_simp_post_weak_rule_thm = store_thm("abstract_simp_post_weak_rule_thm",
  ``!m invariant l ls ls' pre post1 post2.
    weak_model m ==>
    (!ms. (m.pc ms) IN ls ==> (post1 ms) ==> (post2 ms)) ==>
    abstract_simp_jgmt m invariant l ls ls' pre post1 ==>
    abstract_simp_jgmt m invariant l ls ls' pre post2``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
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
  abstract_conseq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);

val abstract_simp_pre_str_rule_thm = store_thm("abstract_simp_pre_str_rule_thm",
  ``!m invariant l ls ls' pre1 pre2 post.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    abstract_simp_jgmt m invariant l ls ls' pre1 post ==>
    abstract_simp_jgmt m invariant l ls ls' pre2 post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
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
  abstract_conseq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val abstract_simp_post_weak_corollary_rule_thm = prove(``
  !m invariant l ls ls' pre post1 post2.
  weak_model m ==>
  abstract_simp_jgmt m invariant l ls ls' pre post1 ==>
  abstract_simp_jgmt m invariant l ls ls' pre (\ms. if m.pc ms IN ls then post1 ms else post2 ms)``,

REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls`, `ls'`, `pre`,  `post1`, 
                     `(\ms. if m.pc ms IN ls then post1 ms else post2 ms)`]
  abstract_simp_post_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val abstract_simp_post_weak_corollary2_rule_thm = prove(``
  !m invariant l ls1 ls2 ls' pre post1 post2.
  weak_model m ==>
  ((ls1 INTER ls2) = EMPTY) ==>
  abstract_simp_jgmt m invariant l ls1 ls' pre post1 ==>
  abstract_simp_jgmt m invariant l ls1 ls' pre (\ms. if (m.pc ms IN ls2) then post2 ms else post1 ms)``,

REPEAT STRIP_TAC >>
subgoal `!ms. m.pc ms IN ls1 ==> post1 ms ==>
         (\ms. if m.pc ms IN ls2 then post2 ms else post1 ms) ms` >- (
  REPEAT STRIP_TAC >>
  METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm]
) >>
ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls'`, `pre`,  `post1`,
                     `\ms. if m.pc ms IN ls2 then post2 ms else post1 ms`]
  abstract_simp_post_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] 
);


val abstract_simp_seq_one_rule_thm = store_thm("abstract_simp_seq_one_rule_thm",
  ``!m invariant l wl1 wl2 bl1 bl2 pre post.
    weak_model m ==>
    (bl1 INTER bl2 = {}) ==>
    abstract_simp_jgmt m invariant l (wl1 UNION wl2) (bl1 UNION bl2) pre post ==>
    (!l1.
     (l1 IN wl1) ==>
     abstract_simp_jgmt m invariant l1 (wl2 UNION bl1) bl2 post post
    ) ==>
    (abstract_simp_jgmt m invariant l (wl2 UNION bl1) bl2 pre post)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
STRIP_TAC >- (
  subgoal `(wl2) INTER (bl2) = {}` >- (
    irule bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm >>
    Q.EXISTS_TAC `bl1 UNION bl2` >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [Once pred_setTheory.INTER_COMM] >>
    irule bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm >>
    Q.EXISTS_TAC `wl1 UNION wl2` >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
  ) >>
  FULL_SIMP_TAC std_ss [Once pred_setTheory.INTER_COMM,
                        pred_setTheory.UNION_OVER_INTER,
                        pred_setTheory.UNION_EMPTY]
) >>
STRIP_TAC >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC [pred_setTheory.MEMBER_NOT_EMPTY]
) >>
irule abstract_seq_rule_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `wl1` >>
STRIP_TAC >| [
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  irule abstract_conseq_rule_thm >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `\ms. m.pc ms NOTIN bl2 /\ post ms /\ invariant ms` >>
  Q.EXISTS_TAC `\ms. post ms /\ invariant ms` >>
  FULL_SIMP_TAC std_ss [],

  irule abstract_conseq_rule_thm >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `\ms. m.pc ms NOTIN bl1 UNION bl2 /\ post ms /\ invariant ms` >>
  Q.EXISTS_TAC `\ms. pre ms /\ invariant ms` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.UNION_ASSOC]
]
);

(* This proof should use the blacklist move lemma *)
val abstract_simp_seq_rule_thm = prove(
  ``!m invariant l ls1 ls ls' pre post.
    weak_model m ==>
    (* TODO: This really needed? *)
    (ls INTER ls' = {}) ==>
    abstract_simp_jgmt m invariant l ls1 (ls UNION ls') pre post ==>
    (!l1.
     (l1 IN ls1) ==>
     abstract_simp_jgmt m invariant l1 ls ls' post post
    ) ==>
    (abstract_simp_jgmt m invariant l ls ls' pre post)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
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
  abstract_conseq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Massage the second contract *)
subgoal `!l1. l1 IN ls1 ==>
         abstract_jgmt m l1 (ls UNION ls') (\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms)
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
    abstract_conseq_rule_thm) >>
  REV_FULL_SIMP_TAC std_ss []
) >>

ASSUME_TAC (Q.SPECL [`m`, `l`, `ls1`, `ls UNION ls'`,
                     `\ms. pre ms /\ invariant ms`,
                     `\ms. m.pc ms NOTIN ls' /\ post ms /\ invariant ms`]
  abstract_seq_rule_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
METIS_TAC [pred_setTheory.MEMBER_NOT_EMPTY]
);


val abstract_simp_std_seq_rule_thm = store_thm("abstract_simp_std_seq_rule_thm",
  ``!m ls1 ls1' ls2 ls2' invariant l pre1 post1 post2.
    weak_model m ==>
    ls1' SUBSET ls2 ==>
    (ls1 INTER ls1' = EMPTY) ==>
    abstract_simp_jgmt m invariant l ls1 ls2 pre1 post1 ==>
    (!l1. (l1 IN ls1) ==> (abstract_simp_jgmt m invariant l1 ls1' ls2' post1 post2)) ==>
    abstract_simp_jgmt m invariant l ls1' (ls2 INTER ls2') pre1 post2``,

REPEAT STRIP_TAC >>
(* First we extend the initial contract to have the same postcondition *)
subgoal `abstract_simp_jgmt m invariant l ls1 ls2 pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  METIS_TAC [abstract_simp_post_weak_corollary_rule_thm]
) >>
(* We then restrict the non-accessible addresses of the first contract *)
subgoal `ls1' UNION (ls2 INTER ls2') SUBSET ls2` >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
) >>
subgoal `abstract_simp_jgmt m invariant l ls1 (ls1' UNION ls2 INTER ls2') pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  METIS_TAC [abstract_simp_bl_subset_rule_thm]
) >>
(* Now, we extend the second contracts *)
subgoal `!l1.
         l1 IN ls1 ==>
         abstract_simp_jgmt m invariant l1 ls1' (ls2 INTER ls2')
           ((\ms. if m.pc ms IN ls1 then post1 ms else post2 ms))
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>  
  REV_FULL_SIMP_TAC std_ss [] >>
  (* Now, we extend the second contract to have the same postcondition *)
  subgoal `abstract_simp_jgmt m invariant l1 ls1' ls2' post1
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
    METIS_TAC [abstract_simp_post_weak_corollary2_rule_thm, pred_setTheory.INTER_COMM]
  ) >>
  (* We then restrict the non-accessible addresses of the first contract *)
  subgoal `abstract_simp_jgmt m invariant l1 ls1' (ls2 INTER ls2') post1
             (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
    METIS_TAC [abstract_simp_bl_subset_rule_thm, pred_setTheory.INTER_SUBSET]
  ) >>
  FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
  irule abstract_conseq_rule_thm >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `\ms.
                  m.pc ms NOTIN ls2 INTER ls2' /\
                  (if m.pc ms IN ls1 then post1 ms else post2 ms) /\
                  invariant ms` >>
  Q.EXISTS_TAC `\ms. post1 ms /\ invariant ms` >>
  FULL_SIMP_TAC std_ss []
) >>
subgoal `abstract_simp_jgmt m invariant l ls1' (ls2 INTER ls2') pre1
           (\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)` >- (
  ASSUME_TAC (Q.SPECL [`m`, `invariant`, `l`, `ls1`, `ls1'`, `(ls2 INTER ls2')`,
                       `pre1`, `(\ms. if m.pc ms IN ls1 then post1 ms else post2 ms)`]
    abstract_simp_seq_rule_thm
  ) >>
  subgoal `!l1. l1 IN ls1 ==> (ls1' INTER ls2' = {})` >- (
    REPEAT STRIP_TAC >>
    METIS_TAC [abstract_simp_jgmt_def]
  ) >>
  subgoal `ls1 <> EMPTY` >- (
    METIS_TAC [abstract_simp_jgmt_def]
  ) >>
  subgoal `ls1' INTER ls2' = {}` >- (
    METIS_TAC [pred_setTheory.MEMBER_NOT_EMPTY]
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
  abstract_simp_post_weak_rule_thm) >>
REV_FULL_SIMP_TAC std_ss []
);


val abstract_simp_loop_rule_thm = store_thm("abstract_simp_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l wl bl invariant C1 var post.
    l NOTIN wl ==> 
    l NOTIN bl ==>
    (!x. abstract_simp_jgmt m invariant l ({l} UNION wl) bl
      (\ms. C1 ms /\ (var ms = (x:num)))
      (\ms. (m.pc ms = l) /\ var ms < x /\ var ms >= 0)) ==>
    abstract_simp_jgmt m (\ms. T) l wl bl (\ms. ~(C1 ms) /\ invariant ms) post ==>
    abstract_simp_jgmt m (\ms. T) l wl bl invariant post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_simp_jgmt_def] >>
irule abstract_loop_rule_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `C1` >>
Q.EXISTS_TAC `var` >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
  [abstract_loop_jgmt_def, Once boolTheory.CONJ_SYM] >>
STRIP_TAC >>
QSPECL_X_ASSUM ``!x. _`` [`x`] >>  
irule abstract_conseq_rule_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `(\ms.
                m.pc ms NOTIN bl /\ ((m.pc ms = l) /\ var ms < x) /\
                invariant ms)` >>
Q.EXISTS_TAC `(\ms. (C1 ms /\ (var ms = x)) /\ invariant ms)` >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.UNION_ASSOC]
);

val _ = export_theory();



