open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logic_auxTheory abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

Definition abstract_partial_jgmt_def:
 abstract_partial_jgmt m (l:'a) (ls:'a->bool) pre post =
 !ms ms'.
  ((m.pc ms) = l) ==>
  pre ms ==>
  m.weak ms ls ms' ==>
  post ms'
End

Theorem abstract_jgmt_imp_partial_triple:
 !m l ls pre post.
 weak_model m ==>
 abstract_jgmt m l ls pre post ==>
 abstract_partial_jgmt m l ls pre post
Proof
FULL_SIMP_TAC std_ss [abstract_jgmt_def, abstract_partial_jgmt_def] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
metis_tac [weak_unique_thm]
QED

Theorem weak_partial_case_rule_thm:
 !m l ls pre post C1.
 abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
 abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
 abstract_partial_jgmt m l ls pre post
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
metis_tac []
QED

Theorem weak_partial_weakening_rule_thm:
 !m. 
 !l ls pre1 pre2 post1 post2.
 weak_model m ==>
 (!ms. ((m.pc ms) = l) ==> pre2 ms ==> pre1 ms) ==>
 (!ms. ((m.pc ms) IN ls) ==> post1 ms ==> post2 ms) ==>
 abstract_partial_jgmt m l ls pre1 post1 ==>
 abstract_partial_jgmt m l ls pre2 post2
Proof
SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_pc_in_thm]
QED

(* TODO Fix this...
Theorem weak_partial_subset_rule_thm:
 !m. !l ls1 ls2 pre post.
 weak_model m ==>
 (!ms. post ms ==> (~(m.pc ms IN ls2))) ==>
 abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
 abstract_partial_jgmt m l ls1 pre post
Proof
rpt strip_tac >>
rfs [abstract_partial_jgmt_def] >>
rpt strip_tac >>
QSPECL_ASSUM ``!ms ms'. _`` [`ms`, `ms'`] >>
rfs [] >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
 fs []
) >>
subgoal `?n. FUNPOW_OPT m.trs n ms = SOME ms'` >- (
 metis_tac [weak_model_def]
) >>
(* TODO: Fix this
IMP_RES_TAC weak_intermediate_labels >>
QSPECL_X_ASSUM ``!ms ms'. _`` [`ms`, `ms''`] >>
rfs [] >>
metis_tac []
*)
cheat
QED
*)

Theorem weak_partial_conj_rule_thm:
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  abstract_partial_jgmt m l ls pre post1 ==>
  abstract_partial_jgmt m l ls pre post2 ==>
  abstract_partial_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
rpt strip_tac >>
metis_tac [weak_unique_thm]
QED

(* Note: exactly abstract_jgmt_imp_partial_triple *)
Theorem total_to_partial:
 !m l ls pre post.
 weak_model m ==>
 abstract_jgmt m l ls pre post ==>
 abstract_partial_jgmt m l ls pre post
Proof
fs [abstract_jgmt_imp_partial_triple]
QED


Theorem weak_partial_seq_rule_thm:
 !m l ls1 ls2 pre post.
 weak_model m ==>
 abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
 (!l1. (l1 IN ls1) ==>
 (abstract_partial_jgmt m l1 ls2 post post)) ==>
 abstract_partial_jgmt m l ls2 pre post
Proof
rpt strip_tac >>
simp [abstract_partial_jgmt_def] >>
rpt strip_tac >>
subgoal `?ms'. m.weak ms (ls1 UNION ls2) ms'` >- (
 (* There is at least ms', possibly another state if ls1 is encountered before *)
 metis_tac [weak_superset_thm, pred_setTheory.UNION_COMM]
) >>
Cases_on `m.pc ms'' IN ls2` >- (
 (* If ls2 was reached without encountering ls1, we win immediately *)
 imp_res_tac weak_union2_thm >>
 subgoal `ms' = ms''` >- (
  metis_tac [weak_unique_thm]
 ) >>
 metis_tac [abstract_partial_jgmt_def]
) >>
subgoal `m.pc ms'' IN ls1` >- (
 imp_res_tac weak_union_pc_not_in_thm >>
  metis_tac [weak_pc_in_thm]
) >>
subgoal `?l1. m.pc ms'' = l1` >- (
 (* Technically requires ls1 non-empty, but if that is the case, we also win immediately *)
 metis_tac []
) >>
subgoal `?ls1'. ls1 UNION ls2 = ls1' UNION ls2 /\ DISJOINT ls1' ls2` >- (
 qexists_tac `ls1 DIFF ls2` >>
 fs [pred_setTheory.DISJOINT_DIFF]
) >>
fs [] >>
subgoal `abstract_jgmt m l (ls1' UNION ls2) (\s. s = ms /\ pre s) (\s. (m.pc s IN ls1' ==> s = ms'') /\ (m.pc s IN ls2 ==> post s))` >- (
 fs [abstract_jgmt_def, abstract_partial_jgmt_def] >>
 qexists_tac `ms''` >>
 fs []
) >>
subgoal `!l1'. (l1' IN ls1') ==> (abstract_jgmt m l1' ls2 (\s. (m.pc s IN ls1' ==> s = ms'') /\ (m.pc s IN ls2 ==> post s)) (\s. (m.pc s IN ls1' ==> s = ms'') /\ (m.pc s IN ls2 ==> post s)))` >- (
 rpt strip_tac >>
 fs [abstract_jgmt_def, abstract_partial_jgmt_def] >>
 rpt strip_tac >>
 res_tac >>
 subgoal `s' = ms''` >- (
  (* Both reached by m.weak ms (ls1 UNION ls2) *)
  metis_tac [weak_unique_thm]
 ) >>
 fs [] >>
 subgoal `m.weak ms'' ls2 ms'` >- (
  (* Since ms'' is a ls1-point encountered between ms and ls2 *)
   metis_tac [weak_inter]
 ) >>
 qexists_tac ‘ms'’ >>
 fs [] >>
 metis_tac [weak_pc_in_thm, pred_setTheory.IN_DISJOINT]
) >>
imp_res_tac abstract_seq_rule_thm >>
gs [abstract_jgmt_def] >>
subgoal `s' = ms'` >- (
 (* Both reached by m.weak ms ls2 *)
  metis_tac [weak_unique_thm]
) >>
subgoal `m.pc ms' IN ls2` >- (
 (* Reached by m.weak ms ls2 *)
  metis_tac [weak_pc_in_thm]
) >>
metis_tac []
QED

Definition weak_partial_loop_contract_def:
  weak_partial_loop_contract m l le invariant C1 =
    (l NOTIN le /\
     abstract_partial_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms)
       (\ms. m.pc ms = l /\ invariant ms))
End

(* Invariant: *)
(* TODO: Is SING useful enough or do we need LEAST? *)
val invariant = ``\s. (SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME s)) /\ invariant s``;


(* Variant: *)
(* TODO: Make different solution so that THE can be removed... *)
val variant = ``\s. THE (ominus (SOME n_l) ($OLEAST (\n. weak_exec_n m ms ({l} UNION le) n = SOME s)))``;

Theorem weak_partial_loop_rule_thm:
 !m.
 weak_model m ==>
 !l le invariant C1 var post.
 weak_partial_loop_contract m l le invariant C1 ==>
 abstract_partial_jgmt m l le (\ms. invariant ms /\ ~(C1 ms)) post ==>
 abstract_partial_jgmt m l le invariant post
Proof
rpt strip_tac >>
simp [abstract_partial_jgmt_def] >>
rpt strip_tac >>
fs [weak_partial_loop_contract_def] >>
(* 0. Establish n_l *)
subgoal `?n_l. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms') = SOME n_l` >- (
 ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
 subgoal `ms <> ms'` >- (
  metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
 ) >>
 irule weak_exec_n_exists_superset >>
 fs []
) >>

(* 1. Prove loop exit contract *)
subgoal `abstract_jgmt m l le (\s'. (^invariant) s' /\ ~(C1 s')) post` >- (
 fs [abstract_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s' <> ms'` >- (
  (* Since pc of s' is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
 ) >>
 subgoal `m.weak s' le ms'` >- (
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 fs [abstract_partial_jgmt_def] >>
 QSPECL_X_ASSUM ``!ms ms'. m.pc ms = l ==> invariant ms /\ ~C1 ms ==> m.weak ms le ms' ==> post ms'`` [`s'`, `ms'`] >>
 gs [] >>
 qexists_tac `ms'` >>
 metis_tac []
) >>

(* 2. Prove loop iteration contract *)
subgoal `abstract_loop_jgmt m l le (^invariant) C1 (^variant)` >- (
 fs [abstract_loop_jgmt_def, abstract_jgmt_def] >>
 rpt strip_tac >>
 subgoal `s <> ms'` >- (
  (* Since pc of s is l, m.weak ms le ms' and l NOTIN le *)
  metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
 ) >>
 (* n_l': the number of encounters of l up to s *)
 subgoal `?n_l'. (OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME s) = SOME n_l' /\ n_l' < n_l` >- (
  metis_tac [weak_exec_sing_least_less]
 ) >>
 (* ms''': next loop point *)
 subgoal `?ms'''. m.weak s ({l} UNION le) ms'''` >- (
  ONCE_REWRITE_TAC [pred_setTheory.UNION_COMM] >>
  irule weak_superset_thm >>
  fs [] >>
  qexists_tac `ms'` >>
  subgoal `DISJOINT {l} le` >- (
   fs []
  ) >>
  metis_tac [weak_inter_exec]
 ) >>
 subgoal `m.pc ms''' = l` >- (
  fs [abstract_partial_jgmt_def] >>
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
   metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm],

   metis_tac []
  ]
 ) >>
 fs [] >>
 rpt strip_tac >| [
  (* By the contract for the looping case *)
  fs [abstract_partial_jgmt_def] >>
  metis_tac [],

  (* By arithmetic *)
  subgoal `(OLEAST n. weak_exec_n m ms ({l} UNION le) n = SOME ms'3') = SOME (SUC n_l')` >- (
   subgoal `ms''' <> ms'` >- (
    metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
   ) >>
   metis_tac [weak_exec_incr_least]
  ) >>
  fs [ominus_def]
 ]
) >>

imp_res_tac abstract_loop_rule_thm >>
fs [abstract_jgmt_def] >>
(* TODO: Should be provable using trs_to_ls m ({l} UNION le) ms n (SUC n_l) = SOME ms' *)
QSPECL_X_ASSUM  ``!s. m.pc s = l ==> _`` [`ms`] >>
subgoal `SING (\n. n < n_l /\ weak_exec_n m ms ({l} UNION le) n = SOME ms)` >- (
 subgoal `weak_exec_n m ms ({l} UNION le) 0 = SOME ms` >- (
  fs [weak_exec_n_def, FUNPOW_OPT_def]
 ) >>
 subgoal `n_l > 0` >- (
  subgoal `ms <> ms'` >- (
   (* Since pc of ms is l, m.weak ms le ms' and l NOTIN le *)
   metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
  ) >>
  metis_tac [weak_exec_least_nonzero]
 ) >>
 (* By uniqueness theorem (stating no duplicate states before ms' is reached) *)
 irule weak_exec_unique_start >>
 fs [] >>
 qexists_tac `ms'` >>
 metis_tac [weak_pc_in_thm, IN_NOT_IN_NEQ_thm]
) >>
gs [] >>
metis_tac [weak_unique_thm]
QED

val _ = export_theory();
