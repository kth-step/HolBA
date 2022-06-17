open HolKernel Parse boolLib bossLib;
open total_program_logicTheory;
open bir_auxiliaryTheory;

open bir_auxiliaryLib;

val _ = new_theory "total_ext_program_logic";

(* Inv is usually the fact that the program is in memory and that
 * the execution mode is the expected one *)
Definition t_ext_jgmt_def:
 t_ext_jgmt m invariant (l:'a) (ls:'a->bool) (ls':'a->bool) pre post =
  (ls INTER ls' = EMPTY /\ ls <> EMPTY /\
   (t_jgmt m l (ls UNION ls')
               (\s. pre s /\ invariant s)
               (\s. if m.ctrl s IN ls'
                    then F
                    else post s /\ invariant s))
  )
End


Theorem total_ext_emb_rule_thm:
 !TS TS' invariant l ls ls' pre post.
  first_enc TS ==>
  first_enc TS' ==>
  (!s ls s'. TS.weak s ls s' ==> TS'.weak s ls s') ==>
  (!s l. TS'.ctrl s = l  ==> TS.ctrl s = l) ==>
  t_ext_jgmt TS invariant l ls ls' pre post ==>
  t_ext_jgmt TS' invariant l ls ls' pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
irule total_emb_rule_thm >>
metis_tac []
QED


Theorem total_ext_el_subset_rule_thm:
 !TS.
  !invariant l ls ls' ls'' pre post.
  first_enc TS ==>
  ls'' SUBSET ls' ==>
  t_ext_jgmt TS invariant l ls ls' pre post ==>
  t_ext_jgmt TS invariant l ls ls'' pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
conj_tac >| [
 irule INTER_SUBSET_EMPTY_thm >>
 qexists_tac `ls'` >>
 fs [],

 ASSUME_TAC (ISPECL [``ls'':'b->bool``, ``ls':'b->bool``] SUBSET_EQ_UNION_thm) >>
 rfs [] >>
 fs [] >>
 subgoal `!s. (\s. TS.ctrl s NOTIN ls'' UNION v /\ post s /\ invariant s) s ==>
          TS.ctrl s NOTIN v` >- (
  rpt strip_tac >>
  fs [] 
 ) >>
 Q.SUBGOAL_THEN `(ls UNION (ls'' UNION v)) = ((ls UNION ls'') UNION v)` (fn thm => fs [thm]) >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
 ) >>
 ASSUME_TAC (Q.SPECL [`TS`, `l`, `ls UNION ls''`, `v`,
                      `\s:'a. pre s /\ invariant s`,
                      `\s:'a. TS.ctrl s NOTIN (ls'':'b->bool) UNION v /\ post s /\ invariant s`] 
  total_subset_rule_thm) >>
 rfs [] >>
 subgoal `!s. TS.ctrl s IN ls UNION ls'' ==>
              (\s. TS.ctrl s NOTIN ls'' UNION v /\ post s /\ invariant s) s ==>
              (\s. TS.ctrl s NOTIN ls'' /\ post s /\ invariant s) s` >- (
  rpt strip_tac >>
  fs []
 ) >>
 irule total_conseq_rule_thm >>
 fs [] >>
 qexistsl_tac [`(\s:'a. TS.ctrl s NOTIN (ls'':'b->bool) UNION v /\ post s /\ invariant s)`,
               `(\s. pre s /\ invariant s)`] >>
 fs []
]
QED


Theorem total_ext_el_to_il_rule_thm:
 !TS invariant l l' ls ls' pre post.
  first_enc TS ==>
  l' IN ls' ==>
  t_ext_jgmt TS invariant l ls ls' pre post ==>
  t_ext_jgmt TS invariant l (l' INSERT ls) (ls' DELETE l') pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
subgoal `?ls''. ls' = l' INSERT ls'' /\ l' NOTIN ls''` >- (
  metis_tac [pred_setTheory.DECOMPOSITION]
) >>
subgoal `l' NOTIN ls` >- (
  CCONTR_TAC >>
  subgoal `?ls'''. ls = l' INSERT ls''' /\ l' NOTIN ls'''` >- (
    metis_tac [pred_setTheory.DECOMPOSITION]
  ) >>
  fs [pred_setTheory.INSERT_INTER]
) >>
rpt strip_tac >| [
  ONCE_REWRITE_TAC [pred_setTheory.INTER_COMM] >>
  fs [pred_setTheory.DELETE_INTER, pred_setTheory.INSERT_INTER,
      pred_setTheory.INSERT_EQ_SING] >>
  fs [Once pred_setTheory.INTER_COMM, pred_setTheory.INSERT_INTER] >>
  fs [Once pred_setTheory.INTER_COMM],

  irule total_conseq_rule_thm >>
  fs [] >>
  qexistsl_tac [`\s. TS.ctrl s NOTIN l' INSERT ls'' /\ post s /\ invariant s`,
                `\s. pre s /\ invariant s`] >>
  `(l' INSERT ls) UNION ((l' INSERT ls'') DELETE l') = ls UNION (l' INSERT ls'')` suffices_by (
    fs []
  ) >>
  metis_tac [pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ,
             pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT]
]
QED


Theorem total_ext_il_to_el_rule_thm:
 !TS invariant l l' ls ls' pre post.
  first_enc TS ==>
  l' IN ls ==>
  ls DELETE l' <> {} ==>
  (!s. TS.ctrl s = l' ==> (post s = F)) ==>
  t_ext_jgmt TS invariant l ls ls' pre post ==>
  t_ext_jgmt TS invariant l (ls DELETE l') (l' INSERT ls') pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
subgoal `?ls''. ls = l' INSERT ls'' /\ l' NOTIN ls''` >- (
 metis_tac [pred_setTheory.DECOMPOSITION]
) >>
subgoal `l' NOTIN ls'` >- (
 metis_tac [pred_setTheory.INSERT_INTER, pred_setTheory.NOT_INSERT_EMPTY]
) >>
rpt strip_tac >| [
 fs [pred_setTheory.DELETE_INTER, pred_setTheory.INSERT_INTER,
     pred_setTheory.COMPONENT] >>
 ONCE_REWRITE_TAC [pred_setTheory.INTER_COMM] >>
 fs [pred_setTheory.INSERT_INTER, pred_setTheory.COMPONENT,
     pred_setTheory.INSERT_EQ_SING] >>
 `ls'' SUBSET ls` suffices_by (
  fs [pred_setTheory.INTER_COMM]
 ) >>
 fs [],

 irule total_conseq_rule_thm >>
 fs [] >>
 qexistsl_tac [`\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s`, `\s. pre s /\ invariant s`] >>
 fs [] >>
 rpt strip_tac >- (
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  Cases_on `TS.ctrl s = l'` >> (
   fs []
  )
 ) >>
 `(l' INSERT ls'') DELETE l' UNION (l' INSERT ls') = (l' INSERT ls'') UNION ls'` suffices_by (
  fs []
 ) >>
 metis_tac [pred_setTheory.UNION_COMM, pred_setTheory.INSERT_UNION_EQ,
            pred_setTheory.DELETE_INSERT, pred_setTheory.DELETE_NON_ELEMENT]
]
QED


Theorem total_ext_il_to_el_set_rule_thm:
 !TS invariant l ls ls' ls'' pre post.
  first_enc TS ==>
  FINITE ls'' ==>
  ls'' PSUBSET ls ==>
  (!s l'.
   l' IN ls'' ==>
   TS.ctrl s = l' ==>
   (post s = F)
  ) ==>
  t_ext_jgmt TS invariant l ls ls' pre post ==>
  t_ext_jgmt TS invariant l (ls DIFF ls'') (ls' UNION ls'') pre post
Proof
rpt strip_tac >>
Induct_on `ls''` >>
rpt strip_tac >- (
 fs []
) >>
subgoal `ls'' PSUBSET ls` >- (
 fs [pred_setTheory.PSUBSET_DEF] >>
 metis_tac [pred_setTheory.NOT_EQUAL_SETS]
) >>
subgoal `e IN ls` >- (
 fs [pred_setTheory.PSUBSET_DEF]
) >>
subgoal `ls DIFF ls'' <> {e}` >- (
 fs [pred_setTheory.PSUBSET_MEMBER] >>
 subgoal `y IN ls DIFF ls''` >- (
  fs [pred_setTheory.IN_DIFF]
 ) >>
 subgoal `y NOTIN {e}` >- (
  fs []
 ) >>
 fs [pred_setTheory.NOT_EQUAL_SETS] >>
 qexists_tac `y` >>
 fs []
) >>
ASSUME_TAC
  (Q.SPECL [`TS`, `invariant`, `l`, `e`, `(ls DIFF ls'')`,
            `(ls' UNION ls'')`, `pre`, `post`] total_ext_il_to_el_rule_thm) >>
rfs [] >>
subgoal `ls DIFF (e INSERT ls'') = (ls DIFF ls'' DELETE e)` >- (
 (* TODO: Proof doesn't go through without these split... *)
 fs [pred_setTheory.DIFF_INSERT] >>
 fs [pred_setTheory.DELETE_DEF, pred_setTheory.DIFF_COMM]
) >>
subgoal `(ls' UNION (e INSERT ls'')) = (e INSERT ls' UNION ls'')` >- (
  ONCE_REWRITE_TAC [pred_setTheory.INSERT_SING_UNION] >>
  metis_tac [pred_setTheory.UNION_COMM, pred_setTheory.UNION_ASSOC]
) >>
fs []
QED


Theorem total_ext_post_weak_rule_thm:
 !TS invariant l ls ls' pre post1 post2.
  first_enc TS ==>
  (!s. (TS.ctrl s) IN ls ==> (post1 s) ==> (post2 s)) ==>
  t_ext_jgmt TS invariant l ls ls' pre post1 ==>
  t_ext_jgmt TS invariant l ls ls' pre post2
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
irule total_conseq_rule_thm >>
fs [] >>
qexistsl_tac [`\s. TS.ctrl s NOTIN (ls':'b->bool) /\ post1 s /\ invariant s`,
              `\s. pre s /\ invariant s`] >>
metis_tac []
QED


Theorem total_ext_pre_str_rule_thm:
 !TS invariant l ls ls' pre1 pre2 post.
  first_enc TS ==>
  (!s. TS.ctrl s = l ==> pre2 s ==> pre1 s) ==>
  t_ext_jgmt TS invariant l ls ls' pre1 post ==>
  t_ext_jgmt TS invariant l ls ls' pre2 post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
irule total_conseq_rule_thm >>
fs [] >>
qexistsl_tac [`\s. TS.ctrl s NOTIN (ls':'b->bool) /\ post s /\ invariant s`,
              `\s. pre1 s /\ invariant s`] >>
metis_tac []
QED


Triviality total_ext_post_weak_corollary_rule_thm:
 !TS invariant l ls ls' pre post1 post2.
  first_enc TS ==>
  t_ext_jgmt TS invariant l ls ls' pre post1 ==>
  t_ext_jgmt TS invariant l ls ls' pre (\s. if TS.ctrl s IN ls then post1 s else post2 s)
Proof
rpt strip_tac >>
irule total_ext_post_weak_rule_thm >>
fs [] >>
qexists_tac `post1` >>
metis_tac []
QED


Triviality total_ext_post_weak_corollary2_rule_thm:
 !TS invariant l ls1 ls2 ls' pre post1 post2.
  first_enc TS ==>
  ls1 INTER ls2 = EMPTY ==>
  t_ext_jgmt TS invariant l ls1 ls' pre post1 ==>
  t_ext_jgmt TS invariant l ls1 ls' pre (\s. if (TS.ctrl s IN ls2) then post2 s else post1 s)
Proof
rpt strip_tac >>
irule total_ext_post_weak_rule_thm >>
fs [] >>
qexists_tac `post1` >>
subgoal `!s. TS.ctrl s IN ls1 ==> post1 s ==>
         (\s. if TS.ctrl s IN ls2 then post2 s else post1 s) s` >- (
 rpt strip_tac >>
 metis_tac [INTER_EMPTY_IN_NOT_IN_thm]
) >>
metis_tac []
QED


Theorem total_ext_seq_one_rule_thm:
 !TS invariant l il1 il2 el1 el2 pre post.
  first_enc TS ==>
  el1 INTER el2 = {} ==>
  t_ext_jgmt TS invariant l (il1 UNION il2) (el1 UNION el2) pre post ==>
  (!l1.
   l1 IN il1 ==>
   t_ext_jgmt TS invariant l1 (il2 UNION el1) el2 post post
  ) ==>
  t_ext_jgmt TS invariant l (il2 UNION el1) el2 pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
strip_tac >- (
 subgoal `il2 INTER el2 = {}` >- (
  irule bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm >>
  Q.EXISTS_TAC `el1 UNION el2` >>
  fs [Once pred_setTheory.INTER_COMM] >>
  irule bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm >>
  Q.EXISTS_TAC `il1 UNION il2` >>
  fs []
 ) >>
 fs [Once pred_setTheory.INTER_COMM,
     pred_setTheory.UNION_OVER_INTER,
     pred_setTheory.UNION_EMPTY]
) >>
strip_tac >- (
 metis_tac [pred_setTheory.MEMBER_NOT_EMPTY]
) >>
irule total_seq_rule_thm >>
fs [] >>
qexists_tac `il1` >>
strip_tac >| [
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>
 irule total_conseq_rule_thm >>
 fs [] >>
 qexistsl_tac [`\s. TS.ctrl s NOTIN el2 /\ post s /\ invariant s`,
               `\s. post s /\ invariant s`] >>
 fs [],

 irule total_conseq_rule_thm >>
 fs [] >>
 qexistsl_tac [`\s. TS.ctrl s NOTIN el1 UNION el2 /\ post s /\ invariant s`,
               `\s. pre s /\ invariant s`] >>
 fs [pred_setTheory.UNION_ASSOC]
]
QED


(* This proof should use the exclude list move lemma *)
Triviality total_ext_seq_rule_thm:
 !TS invariant l ls1 ls ls' pre post.
  first_enc TS ==>
  (* TODO: This really needed? *)
  ls INTER ls' = {} ==>
  t_ext_jgmt TS invariant l ls1 (ls UNION ls') pre post ==>
  (!l1.
   l1 IN ls1 ==>
   t_ext_jgmt TS invariant l1 ls ls' post post
  ) ==>
  t_ext_jgmt TS invariant l ls ls' pre post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
rfs [] >>
(* Massage first contract *)
subgoal `!s. TS.ctrl s IN (ls1 UNION (ls UNION ls')) ==>
         (\s. TS.ctrl s NOTIN ls UNION ls' /\ post s /\ invariant s) s ==>
         (\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s) s` >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
) >>
ASSUME_TAC (Q.SPECL [`TS`, `l`, `ls1 UNION (ls UNION ls')`, `\s. pre s /\ invariant s`,
                     `\s. pre s /\ invariant s`,
                     `\s. TS.ctrl s NOTIN ls UNION ls' /\ post s /\ invariant s`,
                     `\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s`]
  total_conseq_rule_thm) >>
rfs [] >>
(* Massage the second contract *)
subgoal `!l1. l1 IN ls1 ==>
         t_jgmt TS l1 (ls UNION ls') (\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s)
         (\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s)` >- (
  rpt strip_tac >>
  subgoal `!s.
           (TS.ctrl s = l1) ==>
           (\s. post s /\ invariant s) s ==>
           (\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s) s` >- (
    rpt strip_tac >>
    fs [pred_setTheory.UNION_OVER_INTER] >>
    metis_tac [INTER_EMPTY_IN_NOT_IN_thm]
  ) >>
  ASSUME_TAC (Q.SPECL [`TS`, `l1`, `ls UNION ls'`,
                       `\s. post s /\ invariant s`,
                       `\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s`,
                       `\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s`,
                       `\s. TS.ctrl s NOTIN ls' /\ post s /\ invariant s`]
    total_conseq_rule_thm) >>
  rfs []
) >>
conj_tac >| [
 metis_tac [pred_setTheory.MEMBER_NOT_EMPTY],

 irule total_seq_rule_thm >>
 fs [] >>
 qexists_tac `ls1` >>
 rfs []
]
QED


Theorem total_ext_std_seq_rule_thm:
 !TS ls1 ls1' ls2 ls2' invariant l pre1 post1 post2.
  first_enc TS ==>
  ls1' SUBSET ls2 ==>
  ls1 INTER ls1' = EMPTY ==>
  t_ext_jgmt TS invariant l ls1 ls2 pre1 post1 ==>
  (!l1. l1 IN ls1 ==> t_ext_jgmt TS invariant l1 ls1' ls2' post1 post2) ==>
  t_ext_jgmt TS invariant l ls1' (ls2 INTER ls2') pre1 post2
Proof
rpt strip_tac >>
(* First we extend the initial contract to have the same postcondition *)
subgoal `t_ext_jgmt TS invariant l ls1 ls2 pre1
           (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
 metis_tac [total_ext_post_weak_corollary_rule_thm]
) >>
(* We then restrict the non-accessible addresses of the first contract *)
subgoal `ls1' UNION (ls2 INTER ls2') SUBSET ls2` >- (
 fs []
) >>
subgoal `t_ext_jgmt TS invariant l ls1 (ls1' UNION ls2 INTER ls2') pre1
           (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
 metis_tac [total_ext_el_subset_rule_thm]
) >>
(* Now, we extend the second contracts *)
subgoal `!l1.
         l1 IN ls1 ==>
         t_ext_jgmt TS invariant l1 ls1' (ls2 INTER ls2')
          (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)
          (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
  rpt strip_tac >>
  QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>  
  rfs [] >>
  (* Now, we extend the second contract to have the same postcondition *)
  subgoal `t_ext_jgmt TS invariant l1 ls1' ls2' post1
            (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
   metis_tac [total_ext_post_weak_corollary2_rule_thm, pred_setTheory.INTER_COMM]
  ) >>
  (* We then restrict the non-accessible addresses of the first contract *)
  subgoal `t_ext_jgmt TS invariant l1 ls1' (ls2 INTER ls2') post1
            (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
   metis_tac [total_ext_el_subset_rule_thm, pred_setTheory.INTER_SUBSET]
  ) >>
  fs [t_ext_jgmt_def] >>
  irule total_conseq_rule_thm >>
  fs [] >>
  qexistsl_tac [`\s.
                  TS.ctrl s NOTIN ls2 INTER ls2' /\
                  (if TS.ctrl s IN ls1 then post1 s else post2 s) /\
                  invariant s`, `\s. post1 s /\ invariant s`] >>
  fs []
) >>
subgoal `t_ext_jgmt TS invariant l ls1' (ls2 INTER ls2') pre1
          (\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >- (
 ASSUME_TAC (Q.SPECL [`TS`, `invariant`, `l`, `ls1`, `ls1'`, `(ls2 INTER ls2')`,
                      `pre1`, `(\s. if TS.ctrl s IN ls1 then post1 s else post2 s)`]
  total_ext_seq_rule_thm
 ) >>
 subgoal `!l1. l1 IN ls1 ==> (ls1' INTER ls2' = {})` >- (
  rpt strip_tac >>
  metis_tac [t_ext_jgmt_def]
 ) >>
 subgoal `ls1 <> EMPTY` >- (
  metis_tac [t_ext_jgmt_def]
 ) >>
 subgoal `ls1' INTER ls2' = {}` >- (
  metis_tac [pred_setTheory.MEMBER_NOT_EMPTY]
 ) >>
 metis_tac [INTER_EMPTY_INTER_INTER_EMPTY_thm, pred_setTheory.INTER_COMM]
) >>
subgoal `(!s. TS.ctrl s IN ls1' ==>
	  (\s.
	   if TS.ctrl s IN ls1
	   then post1 s
	   else post2 s) s ==>
	   post2 s)` >- (
 rpt strip_tac >>
 fs [] >>
 subgoal `~(TS.ctrl s IN ls1)` >- (
  metis_tac [INTER_EMPTY_IN_NOT_IN_thm]
 ) >>
 fs [] 
) >>
(* Finish everything... *)
irule total_ext_post_weak_rule_thm >>
fs [] >>
qexists_tac `(\s. if TS.ctrl s IN ls1 then post1 s else post2 s)` >>
rfs []
QED


Theorem total_ext_loop_rule_thm:
 !TS.
  first_enc TS ==>
  !l il el invariant C1 var post.
  l NOTIN il ==> 
  l NOTIN el ==>
  (!x. t_ext_jgmt TS invariant l ({l} UNION il) el
    (\s. C1 s /\ (var s = (x:num)))
    (\s. (TS.ctrl s = l) /\ var s < x /\ var s >= 0)) ==>
  t_ext_jgmt TS (\s. T) l il el (\s. ~(C1 s) /\ invariant s) post ==>
  t_ext_jgmt TS (\s. T) l il el invariant post
Proof
rpt strip_tac >>
fs [t_ext_jgmt_def] >>
irule total_loop_rule_thm >>
fs [] >>
qexistsl_tac [`C1`, `var`] >>
fs [total_loop_jgmt_def, Once boolTheory.CONJ_SYM] >>
strip_tac >>
QSPECL_X_ASSUM ``!x. _`` [`x`] >>  
irule total_conseq_rule_thm >>
fs [] >>
qexistsl_tac [`\s.
                TS.ctrl s NOTIN el /\ ((TS.ctrl s = l) /\ var s < x) /\
                invariant s`,
              `(\s. (C1 s /\ (var s = x)) /\ invariant s)`] >>
fs [pred_setTheory.UNION_ASSOC]
QED

val _ = export_theory();



