open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open transition_systemTheory total_program_logicTheory;

val _ = new_theory "partial_program_logic";

Definition p_jgmt_def:
 p_jgmt TS (l:'b) (ls:'b->bool) pre post =
 !s s'.
  TS.ctrl s = l ==>
  pre s ==>
  TS.weak ls s s' ==>
  post s'
End

Theorem t_jgmt_imp_partial_triple:
 !TS l ls pre post.
 first_enc TS ==>
 t_jgmt TS l ls pre post ==>
 p_jgmt TS l ls pre post
Proof
fs [t_jgmt_def, p_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
metis_tac [weak_unique]
QED

Theorem partial_case_rule_thm:
 !TS l ls pre post C1.
 p_jgmt TS l ls (\s. (pre s) /\ (C1 s)) post ==>
 p_jgmt TS l ls (\s. (pre s) /\ (~(C1 s))) post ==>
 p_jgmt TS l ls pre post
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
metis_tac []
QED

Theorem partial_weakening_rule_thm:
 !TS. 
 !l ls pre1 pre2 post1 post2.
 first_enc TS ==>
 (!s. TS.ctrl s = l ==> pre2 s ==> pre1 s) ==>
 (!s. TS.ctrl s IN ls ==> post1 s ==> post2 s) ==>
 p_jgmt TS l ls pre1 post1 ==>
 p_jgmt TS l ls pre2 post2
Proof
simp [p_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_ctrl_in]
QED

Theorem partial_subset_rule_thm:
 !TS. !l ls1 ls2 pre post.
 first_enc TS ==>
 (!s. post s ==> ~(TS.ctrl s IN ls2)) ==>
 p_jgmt TS l (ls1 UNION ls2) pre post ==>
 p_jgmt TS l ls1 pre post
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
rpt strip_tac >>
imp_res_tac weak_superset_thm >>
metis_tac [pred_setTheory.UNION_COMM, weak_union, weak_unique]
QED

Theorem partial_conj_rule_thm:
 !TS.
 first_enc TS ==>
 !l ls pre post1 post2.
 p_jgmt TS l ls pre post1 ==>
 p_jgmt TS l ls pre post2 ==>
 p_jgmt TS l ls pre (\s. post1 s /\ post2 s)
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_unique]
QED

(* TODO: exactly t_jgmt_imp_partial_triple *)
Theorem total_to_partial:
 !TS l ls pre post.
 first_enc TS ==>
 t_jgmt TS l ls pre post ==>
 p_jgmt TS l ls pre post
Proof
fs [t_jgmt_imp_partial_triple]
QED


Theorem partial_seq_rule_thm:
 !TS l ls1 ls2 pre post.
 first_enc TS ==>
 p_jgmt TS l (ls1 UNION ls2) pre post ==>
 (!l1. l1 IN ls1 ==>
   p_jgmt TS l1 ls2 post post
 ) ==>
 p_jgmt TS l ls2 pre post
Proof
rpt strip_tac >>
simp [p_jgmt_def] >>
rpt strip_tac >>
subgoal `?s''. TS.weak (ls1 UNION ls2) s s''` >- (
 (* There is at least s', possibly another state if ls1 is encountered before *)
 metis_tac [weak_superset_thm, pred_setTheory.UNION_COMM]
) >>
Cases_on `TS.ctrl s'' IN ls2` >- (
 (* If ls2 was reached without encountering ls1, we win immediately *)
 imp_res_tac weak_union2 >>
 subgoal `s' = s''` >- (
  metis_tac [weak_unique]
 ) >>
 metis_tac [p_jgmt_def]
) >>
subgoal `TS.ctrl s'' IN ls1` >- (
 imp_res_tac weak_union_ctrl_not_in >>
  metis_tac [weak_ctrl_in]
) >>
subgoal `?l1. TS.ctrl s'' = l1` >- (
 (* Technically requires ls1 non-empty, but if that is the case, we also win immediately *)
 metis_tac []
) >>
subgoal `?ls1'. ls1 UNION ls2 = ls1' UNION ls2 /\ DISJOINT ls1' ls2` >- (
 qexists_tac `ls1 DIFF ls2` >>
 fs [pred_setTheory.DISJOINT_DIFF]
) >>
fs [] >>
subgoal `t_jgmt TS l (ls1' UNION ls2) (\st. st = s /\ pre st) (\st. (TS.ctrl st IN ls1' ==> st = s'') /\ (TS.ctrl st IN ls2 ==> post st))` >- (
 fs [t_jgmt_def, p_jgmt_def] >>
 qexists_tac `s''` >>
 fs []
) >>
subgoal `!l1'. (l1' IN ls1') ==> (t_jgmt TS l1' ls2 (\st. (TS.ctrl st IN ls1' ==> st = s'') /\ (TS.ctrl st IN ls2 ==> post st)) (\st. (TS.ctrl st IN ls1' ==> st = s'') /\ (TS.ctrl st IN ls2 ==> post st)))` >- (
 rpt strip_tac >>
 fs [t_jgmt_def, p_jgmt_def] >>
 rpt strip_tac >>
 res_tac >>
 subgoal `st' = s''` >- (
  (* Both reached by TS.weak s (ls1 UNION ls2) *)
  metis_tac [weak_unique]
 ) >>
 fs [] >>
 subgoal `TS.weak ls2 s'' s'` >- (
  (* Since s'' is a ls1-point encountered between s and ls2 *)
   metis_tac [weak_inter]
 ) >>
 qexists_tac `s'` >>
 fs [] >>
 metis_tac [weak_ctrl_in, pred_setTheory.IN_DISJOINT]
) >>
imp_res_tac total_seq_rule_thm >>
gs [t_jgmt_def] >>
subgoal `s' = st'` >- (
 (* Both reached by TS.weak s ls2 *)
  metis_tac [weak_unique]
) >>
subgoal `TS.ctrl s' IN ls2` >- (
 (* Reached by TS.weak s ls2 *)
  metis_tac [weak_ctrl_in]
) >>
metis_tac []
QED

Definition partial_loop_contract_def:
  partial_loop_contract TS l le invariant C1 =
    (l NOTIN le /\
     p_jgmt TS l ({l} UNION le) (\s. invariant s /\ C1 s)
       (\s. TS.ctrl s = l /\ invariant s))
End

(* Invariant: *)
(* TODO: Is SING useful enough or do we need LEAST? *)
val invariant = ``\st. (SING (\n. n < n_l /\ weak_exec_n TS s ({l} UNION le) n = SOME st)) /\ invariant st``;


(* Variant: *)
(* TODO: Make different solution so that THE can be removed... *)
val variant = ``\st. THE (ominus (SOME n_l) ($OLEAST (\n. weak_exec_n TS s ({l} UNION le) n = SOME st)))``;

Theorem partial_loop_rule_thm:
 !TS.
 first_enc TS ==>
 !l le invariant C1 var post.
 partial_loop_contract TS l le invariant C1 ==>
 p_jgmt TS l le (\st. invariant st /\ ~(C1 st)) post ==>
 p_jgmt TS l le invariant post
Proof
rpt strip_tac >>
simp [p_jgmt_def] >>
rpt strip_tac >>
fs [partial_loop_contract_def] >>
(* 0. Establish n_l *)
subgoal `?n_l. (OLEAST n. weak_exec_n TS s ({l} UNION le) n = SOME s') = SOME n_l` >- (
 ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
 subgoal `s <> s'` >- (
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 irule weak_exec_n_exists_superset >>
 fs []
) >>

(* 1. Prove loop exit contract *)
subgoal `t_jgmt TS l le (\st. (^invariant) st /\ ~(C1 st)) post` >- (
 fs [t_jgmt_def] >>
 rpt strip_tac >>
 subgoal `st <> s'` >- (
  (* Since ctrl of st is l, TS.weak le s st and l NOTIN le *)
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 subgoal `TS.weak le st s'` >- (
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 fs [p_jgmt_def] >>
 QSPECL_X_ASSUM ``!st s'. TS.ctrl st = l ==> invariant st /\ ~C1 st ==> TS.weak le st s' ==> post s'`` [`st`, `s'`] >>
 gs [] >>
 qexists_tac `s'` >>
 metis_tac []
) >>

(* 2. Prove loop iteration contract *)
subgoal `total_loop_jgmt TS l le (^invariant) C1 (^variant)` >- (
 fs [total_loop_jgmt_def, t_jgmt_def] >>
 rpt strip_tac >>
 subgoal `st <> s'` >- (
  (* Since ctrl of st is l, TS.weak le st s' and l NOTIN le *)
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 (* n_l': the number of encounters of l up to st *)
 subgoal `?n_l'. (OLEAST n. weak_exec_n TS s ({l} UNION le) n = SOME st) = SOME n_l' /\ n_l' < n_l` >- (
  metis_tac [weak_exec_sing_least_less]
 ) >>
 (* s''': next loop point *)
 subgoal `?s'''. TS.weak ({l} UNION le) st s'''` >- (
  ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
  irule weak_superset_thm >>
  fs [] >>
  qexists_tac `s'` >>
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 subgoal `TS.ctrl s''' = l` >- (
  fs [p_jgmt_def] >>
  metis_tac []
 ) >>
 qexists_tac `s'''` >>
 subgoal `SING (\n. n < n_l /\ weak_exec_n TS s ({l} UNION le) n = SOME s'3')` >- (
  (* Invariant is kept *)
  (* By uniqueness theorem (stating no duplicate states before s' is reached) *)
  irule weak_exec_uniqueness >>
  fs [] >>
  conj_tac >| [
   qexists_tac `s'` >>
   metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm],

   metis_tac []
  ]
 ) >>
 fs [] >>
 rpt strip_tac >| [
  (* By the contract for the looping case *)
  fs [p_jgmt_def] >>
  metis_tac [],

  (* By arithmetic *)
  subgoal `(OLEAST n. weak_exec_n TS s ({l} UNION le) n = SOME s'3') = SOME (SUC n_l')` >- (
   subgoal `s''' <> s'` >- (
    metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
   ) >>
   metis_tac [weak_exec_incr_least]
  ) >>
  fs [ominus_def]
 ]
) >>

imp_res_tac total_loop_rule_thm >>
fs [t_jgmt_def] >>
(* TODO: Should be provable using trs_to_ls TS ({l} UNION le) s n (SUC n_l) = SOME s' *)
QSPECL_X_ASSUM  ``!s. TS.ctrl s = l ==> _`` [`s`] >>
subgoal `SING (\n. n < n_l /\ weak_exec_n TS s ({l} UNION le) n = SOME s)` >- (
 subgoal `weak_exec_n TS s ({l} UNION le) 0 = SOME s` >- (
  fs [weak_exec_n_def, FUNPOW_OPT_def]
 ) >>
 subgoal `n_l > 0` >- (
  subgoal `s <> s'` >- (
   (* Since ctrl of s is l, TS.weak s le s' and l NOTIN le *)
   metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
  ) >>
  metis_tac [weak_exec_least_nonzero]
 ) >>
 (* By uniqueness theorem (stating no duplicate states before s' is reached) *)
 irule weak_exec_unique_start >>
 fs [] >>
 qexists_tac `s'` >>
 metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
) >>
gs [] >>
metis_tac [weak_unique]
QED

val _ = export_theory();
