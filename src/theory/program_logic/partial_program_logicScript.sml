open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open transition_systemTheory total_program_logicTheory;

val _ = new_theory "partial_program_logic";

Definition p_jgmt_def:
 p_jgmt m (l:'a) (ls:'a->bool) pre post =
 !ms ms'.
  m.ctrl ms = l ==>
  pre ms ==>
  m.weak ls ms ms' ==>
  post ms'
End

Theorem t_jgmt_imp_partial_triple:
 !m l ls pre post.
 first_enc m ==>
 t_jgmt m l ls pre post ==>
 p_jgmt m l ls pre post
Proof
fs [t_jgmt_def, p_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
metis_tac [weak_unique]
QED

Theorem partial_case_rule_thm:
 !m l ls pre post C1.
 p_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
 p_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
 p_jgmt m l ls pre post
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
metis_tac []
QED

Theorem partial_weakening_rule_thm:
 !m. 
 !l ls pre1 pre2 post1 post2.
 first_enc m ==>
 (!ms. m.ctrl ms = l ==> pre2 ms ==> pre1 ms) ==>
 (!ms. m.ctrl ms IN ls ==> post1 ms ==> post2 ms) ==>
 p_jgmt m l ls pre1 post1 ==>
 p_jgmt m l ls pre2 post2
Proof
simp [p_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_ctrl_in]
QED

Theorem partial_subset_rule_thm:
 !m. !l ls1 ls2 pre post.
 first_enc m ==>
 (!ms. post ms ==> ~(m.ctrl ms IN ls2)) ==>
 p_jgmt m l (ls1 UNION ls2) pre post ==>
 p_jgmt m l ls1 pre post
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
rpt strip_tac >>
imp_res_tac weak_superset_thm >>
metis_tac [pred_setTheory.UNION_COMM, weak_union, weak_unique]
QED

Theorem partial_conj_rule_thm:
 !m.
 first_enc m ==>
 !l ls pre post1 post2.
 p_jgmt m l ls pre post1 ==>
 p_jgmt m l ls pre post2 ==>
 p_jgmt m l ls pre (\ms. post1 ms /\ post2 ms)
Proof
rpt strip_tac >>
fs [p_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_unique]
QED

(* TODO: exactly t_jgmt_imp_partial_triple *)
Theorem total_to_partial:
 !m l ls pre post.
 first_enc m ==>
 t_jgmt m l ls pre post ==>
 p_jgmt m l ls pre post
Proof
fs [t_jgmt_imp_partial_triple]
QED


Theorem partial_seq_rule_thm:
 !m l ls1 ls2 pre post.
 first_enc m ==>
 p_jgmt m l (ls1 UNION ls2) pre post ==>
 (!l1. l1 IN ls1 ==>
   p_jgmt m l1 ls2 post post
 ) ==>
 p_jgmt m l ls2 pre post
Proof
rpt strip_tac >>
simp [p_jgmt_def] >>
rpt strip_tac >>
subgoal `?ms'. m.weak (ls1 UNION ls2) ms ms'` >- (
 (* There is at least ms', possibly another state if ls1 is encountered before *)
 metis_tac [weak_superset_thm, pred_setTheory.UNION_COMM]
) >>
Cases_on `m.ctrl ms'' IN ls2` >- (
 (* If ls2 was reached without encountering ls1, we win immediately *)
 imp_res_tac weak_union2 >>
 subgoal `ms' = ms''` >- (
  metis_tac [weak_unique]
 ) >>
 metis_tac [p_jgmt_def]
) >>
subgoal `m.ctrl ms'' IN ls1` >- (
 imp_res_tac weak_union_ctrl_not_in >>
  metis_tac [weak_ctrl_in]
) >>
subgoal `?l1. m.ctrl ms'' = l1` >- (
 (* Technically requires ls1 non-empty, but if that is the case, we also win immediately *)
 metis_tac []
) >>
subgoal `?ls1'. ls1 UNION ls2 = ls1' UNION ls2 /\ DISJOINT ls1' ls2` >- (
 qexists_tac `ls1 DIFF ls2` >>
 fs [pred_setTheory.DISJOINT_DIFF]
) >>
fs [] >>
subgoal `t_jgmt m l (ls1' UNION ls2) (\s. s = ms /\ pre s) (\s. (m.ctrl s IN ls1' ==> s = ms'') /\ (m.ctrl s IN ls2 ==> post s))` >- (
 fs [t_jgmt_def, p_jgmt_def] >>
 qexists_tac `ms''` >>
 fs []
) >>
subgoal `!l1'. (l1' IN ls1') ==> (t_jgmt m l1' ls2 (\s. (m.ctrl s IN ls1' ==> s = ms'') /\ (m.ctrl s IN ls2 ==> post s)) (\s. (m.ctrl s IN ls1' ==> s = ms'') /\ (m.ctrl s IN ls2 ==> post s)))` >- (
 rpt strip_tac >>
 fs [t_jgmt_def, p_jgmt_def] >>
 rpt strip_tac >>
 res_tac >>
 subgoal `s' = ms''` >- (
  (* Both reached by m.weak ms (ls1 UNION ls2) *)
  metis_tac [weak_unique]
 ) >>
 fs [] >>
 subgoal `m.weak ls2 ms'' ms'` >- (
  (* Since ms'' is a ls1-point encountered between ms and ls2 *)
   metis_tac [weak_inter]
 ) >>
 qexists_tac `ms'` >>
 fs [] >>
 metis_tac [weak_ctrl_in, pred_setTheory.IN_DISJOINT]
) >>
imp_res_tac total_seq_rule_thm >>
gs [t_jgmt_def] >>
subgoal `s' = ms'` >- (
 (* Both reached by m.weak ms ls2 *)
  metis_tac [weak_unique]
) >>
subgoal `m.ctrl ms' IN ls2` >- (
 (* Reached by m.weak ms ls2 *)
  metis_tac [weak_ctrl_in]
) >>
metis_tac []
QED

Definition partial_loop_contract_def:
  partial_loop_contract m l le invariant C1 =
    (l NOTIN le /\
     p_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms)
       (\ms. m.ctrl ms = l /\ invariant ms))
End

(* Invariant: *)
(* TODO: Is SING useful enough or do we need LEAST? *)
val invariant = ``\s. (SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME s)) /\ invariant s``;


(* Variant: *)
(* TODO: Make different solution so that THE can be removed... *)
val variant = ``\s. THE (ominus (SOME n_l) ($OLEAST (\n. weak_exec_n m ms ({l} UNION le) n = SOME s)))``;

Theorem partial_loop_rule_thm:
 !m.
 first_enc m ==>
 !l le invariant C1 var post.
 partial_loop_contract m l le invariant C1 ==>
 p_jgmt m l le (\ms. invariant ms /\ ~(C1 ms)) post ==>
 p_jgmt m l le invariant post
Proof
rpt strip_tac >>
simp [p_jgmt_def] >>
rpt strip_tac >>
fs [partial_loop_contract_def] >>
(* 0. Establish n_l *)
subgoal `?n_l. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms') = SOME n_l` >- (
 ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
 subgoal `ms <> ms'` >- (
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 irule weak_exec_n_exists_superset >>
 fs []
) >>

(* 1. Prove loop exit contract *)
subgoal `t_jgmt m l le (\s'. (^invariant) s' /\ ~(C1 s')) post` >- (
 fs [t_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s' <> ms'` >- (
  (* Since ctrl of s' is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 subgoal `m.weak le s' ms'` >- (
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 fs [p_jgmt_def] >>
 QSPECL_X_ASSUM ``!ms ms'. m.ctrl ms = l ==> invariant ms /\ ~C1 ms ==> m.weak le ms ms' ==> post ms'`` [`s'`, `ms'`] >>
 gs [] >>
 qexists_tac `ms'` >>
 metis_tac []
) >>

(* 2. Prove loop iteration contract *)
subgoal `total_loop_jgmt m l le (^invariant) C1 (^variant)` >- (
 fs [total_loop_jgmt_def, t_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s <> ms'` >- (
  (* Since ctrl of s is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
 ) >>
 (* n_l': the number of encounters of l up to s *)
 subgoal `?n_l'. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME s) = SOME n_l' /\ n_l' < n_l` >- (
  metis_tac [weak_exec_sing_least_less]
 ) >>
 (* ms''': next loop point *)
 subgoal `?ms'''. m.weak ({l} UNION le) s ms'''` >- (
  ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
  irule weak_superset_thm >>
  fs [] >>
  qexists_tac `ms'` >>
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 subgoal `m.ctrl ms''' = l` >- (
  fs [p_jgmt_def] >>
  metis_tac []
 ) >>
 qexists_tac `ms'''` >>
 subgoal `SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME ms'3')` >- (
  (* Invariant is kept *)
  (* By uniqueness theorem (stating no duplicate states before ms' is reached) *)
  irule weak_exec_uniqueness >>
  fs [] >>
  conj_tac >| [
   qexists_tac `ms'` >>
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
  subgoal `(OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms'3') = SOME (SUC n_l')` >- (
   subgoal `ms''' <> ms'` >- (
    metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
   ) >>
   metis_tac [weak_exec_incr_least]
  ) >>
  fs [ominus_def]
 ]
) >>

imp_res_tac total_loop_rule_thm >>
fs [t_jgmt_def] >>
(* TODO: Should be provable using trs_to_ls m ({l} UNION le) ms n (SUC n_l) = SOME ms' *)
QSPECL_X_ASSUM  ``!s. m.ctrl s = l ==> _`` [`ms`] >>
subgoal `SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME ms)` >- (
 subgoal `weak_exec_n m ms ({l} UNION le) 0 = SOME ms` >- (
  fs [weak_exec_n_def, FUNPOW_OPT_def]
 ) >>
 subgoal `n_l > 0` >- (
  subgoal `ms <> ms'` >- (
   (* Since ctrl of ms is l, m.weak ms le ms' and l NOTIN le *)
   metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
  ) >>
  metis_tac [weak_exec_least_nonzero]
 ) >>
 (* By uniqueness theorem (stating no duplicate states before ms' is reached) *)
 irule weak_exec_unique_start >>
 fs [] >>
 qexists_tac `ms'` >>
 metis_tac [weak_ctrl_in, IN_NOT_IN_NEQ_thm]
) >>
gs [] >>
metis_tac [weak_unique]
QED

val _ = export_theory();
