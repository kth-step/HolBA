open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logic_auxTheory abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

Definition ominus_def:
 (ominus NONE _ = NONE) /\
 (ominus _ NONE = NONE) /\
 (ominus (SOME (n:num)) (SOME n') = SOME (n - n'))
End

Definition weak_exec_def:
 (weak_exec m ls ms =
  let
   MS' = m.weak ms ls
  in
   if MS' = {}
   then NONE
   else SOME (CHOICE MS'))
End

Definition weak_exec_n_def:
 (weak_exec_n m ms ls n = FUNPOW_OPT (weak_exec m ls) n ms)
End

Theorem FUNPOW_OPT_split:
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n - n') s = SOME s'' ==>
FUNPOW_OPT f n' s'' = SOME s'
Proof
rpt strip_tac >>
irule FUNPOW_OPT_INTER >>
qexistsl_tac [`s`, `n - n'`] >>
fs []
QED

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
 (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
 (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
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

Theorem weak_superset_thm:
 !m.
 weak_model m ==>
 !ms ms' ls1 ls2.
 m.weak ms ls1 ms' ==>
 ?ms''. m.weak ms (ls1 UNION ls2) ms''
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
Cases_on `(OLEAST n'. ?ms''. n' > 0 /\ n' < n /\ FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' IN ls2)` >- (
 fs [] >>
 qexistsl_tac [`ms'`, `n`] >>
 fs [] >>
 rpt strip_tac >>
 fs [whileTheory.OLEAST_EQ_NONE] >>
 metis_tac []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
qexistsl_tac [`ms''`, `x`] >>
fs [] >>
rpt strip_tac >>
QSPECL_X_ASSUM  ``!n'.
         n' < n /\ n' > 0 ==>
         ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n''`] >>
gs [] >>
QSPECL_X_ASSUM  ``!n'.
         n' < x ==>
         !ms'4'.
           FUNPOW_OPT m.trs n' ms = SOME ms'4' ==>
           ~(n' > 0) \/ m.pc ms'4' NOTIN ls2`` [`n''`] >>
gs []
QED

Theorem weak_nonempty:
 !m.
 weak_model m ==>
 !ms ls. 
 m.weak ms ls <> {} <=> (?ms'. m.weak ms ls ms')
Proof
rpt strip_tac >>
fs [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
eq_tac >> (rpt strip_tac) >| [
 qexists_tac `x` >>
 fs [pred_setTheory.IN_APP],

 qexists_tac `ms'` >>
 fs [pred_setTheory.IN_APP]
]
QED

Theorem weak_exec_exists:
 !m.
 weak_model m ==>
 !ms ls ms'. 
 m.weak ms ls ms' <=>
 weak_exec m ls ms = SOME ms'
Proof
rpt strip_tac >>
fs [weak_exec_def] >>
eq_tac >> (
 strip_tac
) >| [
 subgoal `m.weak ms ls = {ms'}` >- (
  fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING, pred_setTheory.IN_APP] >>
  metis_tac [weak_unique_thm]
 ) >>
 fs [],

 metis_tac [pred_setTheory.CHOICE_DEF, pred_setTheory.IN_APP]
]
QED

Theorem weak_exec_to_n:
 !m.
 weak_model m ==>
 !ms ls ms'. 
 weak_exec m ls ms = SOME ms' <=>
 weak_exec_n m ms ls 1 = SOME ms'
Proof
rpt strip_tac >>
fs [weak_exec_n_def, FUNPOW_OPT_def]
QED

Theorem weak_inter:
 !m.
 weak_model m ==>
 !ms ms' ms'' ls1 ls2.
 DISJOINT ls1 ls2 ==>
 m.weak ms ls2 ms' ==>
 m.weak ms (ls1 UNION ls2) ms'' ==>
 m.pc ms'' IN ls1 ==>
 m.weak ms'' ls2 ms'
Proof
rpt strip_tac >>
(* ms goes to ms' in n steps. ms goes to ms'' in n' steps, for which:
 * n'>n: impossible, by the first-encounter property
 * n=n': impossible, since ms' is in ls2 and ms'' is in ls1 (disjoint sets)
 * n'<n: then ms' can be reached by taking n'-n steps, with no ls2-encounters
 * in-between *)
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
subgoal `~(n'>n)` >- (
 QSPECL_X_ASSUM ``!n''.
          n'' < n' /\ n'' > 0 ==>
          ?ms'3'.
            FUNPOW_OPT m.trs n'' ms = SOME ms'3' /\ m.pc ms'3' NOTIN ls1 /\
            m.pc ms'3' NOTIN ls2`` [`n`] >>
 gs []
) >>
subgoal `~(n'=n)` >- (
 strip_tac >>
 gs [] >>
 metis_tac [pred_setTheory.IN_DISJOINT]
) >>
subgoal `n'<n` >- (
 fs []
) >>
qexists_tac `n-n'` >>
rpt strip_tac >| [
 fs [],

 (* by combining execution *)
 irule FUNPOW_OPT_split2 >>
 fs [] >>
 qexists_tac `ms` >>
 fs [],

 (* non-encounter in earlier steps *)
 QSPECL_X_ASSUM ``!n'.
          n' < n /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n' + n''`] >>
 gs [] >>
 qexists_tac `ms'''` >>
 fs [] >>
 metis_tac [FUNPOW_OPT_INTER, arithmeticTheory.ADD_COMM]
]
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
SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
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
 qexists_tac ‘ms''’ >>
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

Theorem weak_least_trs:
 !m ms ls ms'.
 weak_model m ==>
 ms <> ms' ==>
 m.weak ms ls ms' ==>
 ?n'. n' > 0 /\ (OLEAST n'. FUNPOW_OPT m.trs n' ms = SOME ms') = SOME n'
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
qexists_tac `n` >>
fs [whileTheory.OLEAST_EQ_SOME] >>
rpt strip_tac >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
gs [] >>
subgoal `n' = 0` >- (
 fs []
) >>
rw [] >>
gs [FUNPOW_OPT_compute]
QED

Theorem weak_exec_n_prev:
 !m.
 weak_model m ==>
 !ms ls ms' n_l.
 weak_exec_n m ms ls (SUC n_l) = SOME ms' ==>
 ?ms''. weak_exec_n m ms ls n_l = SOME ms'' /\ weak_exec_n m ms'' ls 1 = SOME ms'
Proof
rpt strip_tac >>
fs [weak_exec_n_def] >>
subgoal `SUC n_l > 0` >- (
 fs []
) >>
imp_res_tac FUNPOW_OPT_prev_EXISTS >>
QSPECL_X_ASSUM ``!n'. _`` [`n_l`] >>
fs [] >>
Cases_on `n_l = 0` >- (
 gs [FUNPOW_OPT_compute]
) >>
irule FUNPOW_OPT_split >>
qexistsl_tac [`SUC n_l`, `ms`] >>
fs [arithmeticTheory.ADD1]
QED


Theorem FUNPOW_OPT_cycle:
 !f s s' n n'.
 (OLEAST n. n > 0 /\ FUNPOW_OPT f n s = SOME s) = SOME n ==>
 s <> s' ==>
 (OLEAST n'. FUNPOW_OPT f n' s = SOME s') = SOME n' ==>
 n' < n
Proof
rpt strip_tac >>
CCONTR_TAC >>
Cases_on `n' = n` >- (
 fs [whileTheory.OLEAST_EQ_SOME]
) >>
subgoal `n' > n` >- (
 gs []
) >>
subgoal `FUNPOW_OPT f (n' - n) s = SOME s'` >- (
 irule FUNPOW_OPT_split2 >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `s` >>
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT f n'' s <> SOME s'`` [`n' - n`] >>
gs []
QED

Theorem weak_exec_n_cycle:
 !m s s' ls n_l n_l'.
 weak_model m ==>
 (OLEAST n_l. n_l > 0 /\ weak_exec_n m s ls n_l = SOME s) = SOME n_l ==>
 s <> s' ==>
 (OLEAST n_l'. weak_exec_n m s ls n_l' = SOME s') = SOME n_l' ==>
 n_l' < n_l
Proof
rpt strip_tac >>
fs [weak_exec_n_def] >>
metis_tac [FUNPOW_OPT_cycle]
QED

(* TODO: Useful?
Theorem weak_exec_n_split:
!m. weak_model m ==>
!s s' s'' ls n n'.
n > n' ==>
weak_exec_n m s ls n = SOME s' ==>
weak_exec_n m s ls (n - n') = SOME s'' ==>
weak_exec_n m s'' ls n' = SOME s'
Proof
cheat
QED
*)

Theorem weak_exec_n_split2:
!m. weak_model m ==>
!s s' s'' ls n n'.
n >= n' ==>
weak_exec_n m s ls n' = SOME s'' ==>
weak_exec_n m s ls n = SOME s' ==>
weak_exec_n m s'' ls (n - n') = SOME s'
Proof
rpt strip_tac >>
fs [weak_exec_n_def] >>
Cases_on `n = n'` >- (
 fs [FUNPOW_OPT_compute]
) >>
subgoal `n > n'` >- (
 fs []
) >>
metis_tac [FUNPOW_SUB, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
QED


Theorem weak_exec_n_cycle_alt:
 !m s s' ls n_l n_l'.
 weak_model m ==>
 n_l > 0 /\ weak_exec_n m s ls n_l = SOME s ==>
 s <> s' ==>
 (OLEAST n_l'. weak_exec_n m s ls n_l' = SOME s') = SOME n_l' ==>
 n_l' < n_l
Proof
rpt strip_tac >>
CCONTR_TAC >>
Cases_on `n_l' = n_l` >- (
 fs [whileTheory.OLEAST_EQ_SOME]
) >>
subgoal `n_l' > n_l` >- (
 gs []
) >>
subgoal `weak_exec_n m s ls (n_l' - n_l) = SOME s'` >- (
 irule weak_exec_n_split2 >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `s` >>
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
QSPECL_X_ASSUM ``!n_l''. n_l'' < n_l' ==> weak_exec_n m s ls n_l'' <> SOME s'`` [`n_l' - n_l`] >>
gs []
QED

(* TODO: Technically, this doesn't need OLEAST for the encounter of ms'
 * Let this rely on sub-lemma for incrementing weak_exec_n instead
 * of reasoning on FUNPOW_OPT *)
Theorem weak_exec_incr_last:
 !m.
 weak_model m ==>
 !ms ls ms' n_l ms''.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 m.weak ms' ls ms'' ==>
 weak_exec_n m ms ls (SUC n_l) = SOME ms''
Proof
rpt strip_tac >>
simp [weak_exec_n_def, arithmeticTheory.ADD1] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
irule FUNPOW_OPT_ADD_thm >>
qexists_tac `ms'` >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def] >>
simp [FUNPOW_OPT_def] >>
metis_tac [weak_exec_exists]
QED

Theorem weak_exec_incr_first:
 !m.
 weak_model m ==>
 !ms ls ms' n_l ms''.
 m.weak ms ls ms' ==>
 (OLEAST n. weak_exec_n m ms' ls n = SOME ms'') = SOME n_l ==>
 weak_exec_n m ms ls (SUC n_l) = SOME ms''
Proof
rpt strip_tac >>
simp [weak_exec_n_def, arithmeticTheory.ADD1] >>
irule FUNPOW_OPT_ADD_thm >>
qexists_tac `ms'` >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def] >>
simp [FUNPOW_OPT_def] >>
metis_tac [weak_exec_exists]
QED

Theorem weak_union_pc:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms''.
 m.weak ms ls2 ms' ==>
 m.weak ms (ls1 UNION ls2) ms'' ==>
 ms' <> ms'' ==>
 m.pc ms'' IN ls1
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
Cases_on `n' > n` >- (
 QSPECL_X_ASSUM ``!n''.
          n'' < n' /\ n'' > 0 ==>
          ?ms'3'.
            FUNPOW_OPT m.trs n'' ms = SOME ms'3' /\ m.pc ms'3' NOTIN ls1 /\
            m.pc ms'3' NOTIN ls2`` [`n`] >>
 gs []
) >>
Cases_on `n' = n` >- (
 gs []
) >>
QSPECL_X_ASSUM ``!n'.
          n' < n /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n'`] >>
gs []
QED

Theorem weak_exec_n_add:
!m. weak_model m ==>
!s s' s'' ls n n'.
weak_exec_n m s ls n = SOME s' ==>
weak_exec_n m s' ls n' = SOME s'' ==>
weak_exec_n m s ls (n + n') = SOME s''
Proof
rpt strip_tac >>
fs [weak_exec_n_def] >>
metis_tac [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM]
QED

Theorem weak_exec_n_inter:
 !m.
 weak_model m ==>
 !ms ms' ls1 ls2 n_l n_l'.
 DISJOINT ls1 ls2 ==>
 weak_exec_n m ms ls2 1 = SOME ms' ==>
 (OLEAST n_l. weak_exec_n m ms (ls1 UNION ls2) n_l = SOME ms') = SOME n_l ==>
 n_l' < n_l ==>
 !ms''.
 (OLEAST n_l. weak_exec_n m ms (ls1 UNION ls2) n_l = SOME ms'') = SOME n_l' ==>
 weak_exec_n m ms'' ls2 1 = SOME ms'
Proof
ntac 7 strip_tac >>
Induct_on `n_l'` >- (
 rpt strip_tac >>
 fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def, FUNPOW_OPT_compute]
) >>
rpt strip_tac >>
gs [whileTheory.OLEAST_EQ_SOME] >>
imp_res_tac weak_exec_n_prev >>
QSPECL_X_ASSUM ``!ms'3'.
          weak_exec_n m ms (ls1 UNION ls2) n_l' = SOME ms'3' /\
          (!n_l.
             n_l < n_l' ==>
             weak_exec_n m ms (ls1 UNION ls2) n_l <> SOME ms'3') ==>
          weak_exec_n m ms'3' ls2 1 = SOME ms'`` [`ms'''`] >>
gs [] >>
subgoal `!n_l. n_l < n_l' ==> weak_exec_n m ms (ls1 UNION ls2) n_l <> SOME ms'3'` >- (
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n_l.
          n_l < SUC n_l' ==>
          weak_exec_n m ms (ls1 UNION ls2) n_l <> SOME ms''`` [`SUC n_l''`] >>
 gs [] >>
 metis_tac [weak_exec_n_add, arithmeticTheory.ADD1]
) >>
fs [] >>
(* TODO: Build together that you can proceed one weak transition to superset from ms''',
 * and from the reach ms' whith next weak transition to ls2 *)
(* See reasoning in weak_inter *)
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_to_n thm)]) >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
irule weak_inter >>
fs [] >>
qexistsl_tac [`ls1`, `ms'''`] >>
fs [] >>
subgoal `ms' <> ms''` >- (
QSPECL_X_ASSUM ``!n_l'.
          n_l' < n_l ==> weak_exec_n m ms (ls1 UNION ls2) n_l' <> SOME ms'`` [`SUC n_l'`] >>
 gs []
) >>
metis_tac [weak_union_pc]
QED

Theorem weak_inter_exec:
 !m.
 weak_model m ==>
 !ms ls1 ls2 n_l ms' ms''.
 m.weak ms ls2 ms' ==>
 DISJOINT ls1 ls2 ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n_l ==>
 SING (\n. n < n_l /\ weak_exec_n m ms (ls1 UNION ls2) n = SOME ms'') ==>
 m.weak ms'' ls2 ms'
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_exec_exists thm]) >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_exec_to_n thm]) >>
irule weak_exec_n_inter >>
fs [pred_setTheory.SING_DEF, whileTheory.OLEAST_EQ_SOME] >>
fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING] >>
qexistsl_tac [`ls1`, `ms`, `n_l`, `x`] >>
fs [] >>
rpt strip_tac >>
QSPECL_X_ASSUM  ``!y. y < n_l /\ weak_exec_n m ms (ls1 UNION ls2) y = SOME ms'' ==> x = y`` [`n_l'`] >>
subgoal `n_l' < n_l` >- (
 gs []
) >>
fs []
QED

Theorem weak_subset:
 !m. weak_model m ==>
 !ms ls1 ls2 ms'.
   m.weak ms (ls1 UNION ls2) ms' ==>
   ls1 SUBSET ls2 ==>
   m.weak ms ls2 ms'
Proof
rpt strip_tac >>
fs [pred_setTheory.SUBSET_UNION_ABSORPTION]
QED

Theorem weak_exec_n_OLEAST_equiv:
 !m. weak_model m ==>
 !s ls s'.
  (OLEAST n_l. n_l > 0 /\ weak_exec_n m s ls n_l = SOME s') = SOME 1 ==>
  m.weak s ls s'
Proof
rpt strip_tac >>
fs [whileTheory.OLEAST_EQ_SOME] >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_to_n thm)]) >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)])
QED

(* Continuing weak_exec_n at s'', intermediately between s and s'' *)
Theorem weak_exec_n_OLEAST_inter:
 !m. weak_model m ==>
 !s s' s'' ls n' n'' n_l.
 (OLEAST n'. FUNPOW_OPT m.trs n' s = SOME s') = SOME n' ==>
 (OLEAST n''. n'' > 0 /\ FUNPOW_OPT m.trs n'' s = SOME s'') = SOME n'' ==>
 n' > n'' ==>
 (OLEAST n_l. n_l > 0 /\ weak_exec_n m s ls n_l = SOME s'') = SOME 1 ==>
 (OLEAST n_l. weak_exec_n m s'' ls n_l = SOME s') = SOME n_l ==>
 (OLEAST n_l. weak_exec_n m s ls n_l = SOME s') = SOME (n_l + 1)
Proof
rpt strip_tac >>
simp [whileTheory.OLEAST_EQ_SOME] >>
conj_tac >| [
 metis_tac [arithmeticTheory.ADD1, weak_exec_incr_first, weak_exec_n_OLEAST_equiv],

 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `s <> s'` >- (
  QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT m.trs n'' s <> SOME s'`` [`0`] >>
  subgoal `0 < n'` >- (
   fs []
  ) >>
  gs [FUNPOW_OPT_compute]
 ) >>
 subgoal `s'' <> s'` >- (
  QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT m.trs n'' s <> SOME s'`` [`n''`] >>
  gs []
 ) >>
 subgoal `n_l > 0` >- (
  Cases_on `n_l = 0` >- (
   fs [weak_exec_n_def, FUNPOW_OPT_compute]
  ) >>
  fs []
 ) >>
 `weak_exec_n m s ls 1 <> SOME s' /\ !n_l'. n_l' < n_l ==> weak_exec_n m s'' ls n_l' <> SOME s'` suffices_by (
  rpt strip_tac >>
  fs [] >>
  QSPECL_X_ASSUM ``!n_l'. n_l' < n_l ==> weak_exec_n m s'' ls n_l' <> SOME s'`` [`n_l' - 1`] >>
  gs [] >>
  subgoal `n_l' >= 1` >- (
   Cases_on `n_l' = 0` >- (
    fs [weak_exec_n_def, FUNPOW_OPT_compute]
   ) >>
   fs []
  ) >>
  metis_tac [weak_exec_n_split2]
 ) >>
 QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT m.trs n'' s <> SOME s'`` [`n''`] >>
 gs [] 
]
QED

Theorem weak_exec_1_superset_lemma:
 !m.
 weak_model m ==>
 !ls1 ls2 s'.
 !n n'. n' <= n ==>
        n' >= 1 ==>
        !s. m.weak s ls1 s' /\ ((OLEAST n'. FUNPOW_OPT m.trs n' s = SOME s') = SOME n') ==>
        s <> s' ==>
        ls1 SUBSET ls2 ==>
        ?n_l. n_l >= 1 /\ (OLEAST n_l. weak_exec_n m s ls2 n_l = SOME s') = SOME n_l
Proof
ntac 5 strip_tac >>
Induct_on `n` >- (
 fs []
) >>
rpt strip_tac >>
Cases_on `n' < SUC n` >- (
 QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
 gs []
) >>
subgoal `n' = SUC n` >- (
 fs [] 
) >>
Cases_on `n = 0` >- (
 gs [] >>
 subgoal `n' = 1` >- (
  fs [] 
 ) >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `1` >>
 fs [] >>
 conj_tac >| [
  PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_to_n thm)]) >>
  PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
  PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
  qexists_tac `1` >>
  fs [] >>
  metis_tac [weak_pc_in_thm, pred_setTheory.SUBSET_THM],

  rpt strip_tac >>
  subgoal `n_l' = 0` >- (
   fs [] 
  ) >>
  fs [weak_exec_n_def, FUNPOW_OPT_compute]
 ]
) >>
(* 1. There exists a state s'' which we go to with weak-ls2 from s. (weak_superset_thm should suffice)
 * s'' is reached with more trs than s': contradiction.
 * s'' is reached with same amount of trs as s': s'' is s', proof completed
 * with witness n_l''.
 * s'' is reached with fewer trs than s': use induction hypothesis specialised for s'', then add
 * numbers of weak-ls2 transitions together for the witness. *)
subgoal `?s''. (OLEAST n_l''. n_l'' > 0 /\ weak_exec_n m s ls2 n_l'' = SOME s'') = SOME 1` >- (
 subgoal `?ms''. m.weak s (ls1 UNION ls2) ms''` >- (
  metis_tac [weak_superset_thm]
 ) >>
 qexistsl_tac [`ms''`] >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_subset, weak_exec_to_n, weak_exec_exists]
) >>
subgoal `?n''. (OLEAST n''. n'' > 0 /\ FUNPOW_OPT m.trs n'' s = SOME s'') = SOME n''` >- (
 (* Since s'' is reached by non-zero weak transitions, there must be a (least) non-zero number of trs
  * that reaches it *)
 fs [whileTheory.OLEAST_EQ_SOME] >>
 PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_to_n thm)]) >>
 PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 qexists_tac `n'''` >>
 fs [] >>
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n'.
          n' < n'3' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n''''`] >>
 gs []
) >>
(* s'' is reached with more trs than s': contradiction, s' would have been crossed *)
Cases_on `n'' > n'` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `m.weak s ls2 s''` >- (
  metis_tac [weak_exec_to_n, weak_exec_exists]
 ) >>
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'4' = n''` (fn thm => fs [thm]) >- (
  Cases_on `n'' < n'4'` >- (
   QSPECL_X_ASSUM ``!n'.
          n' < n'4' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n''`] >>
   gs []
  ) >>
  Cases_on `n'' > n'4'` >- (
   QSPECL_X_ASSUM ``!n'3'.
          n'3' < n'' ==> FUNPOW_OPT m.trs n'3' s = SOME s'' ==> ~(n'3' > 0)`` [`n''''`] >>
   gs []
  ) >>
  fs []
 ) >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'3' = n'` (fn thm => fs [thm]) >- (
  Cases_on `n' < n'3'` >- (
   QSPECL_X_ASSUM ``!n'.
          n' < n'3' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'`] >>
   gs []
  ) >>
  Cases_on `n' > n'3'` >- (
   QSPECL_X_ASSUM ``!n'.
          n' < n'3' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'''`] >>
   gs []
  ) >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!n'.
          n' < n'' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n'`] >>
 gs [] >>
 metis_tac [pred_setTheory.SUBSET_THM]
) >>
Cases_on `n'' = n'` >- (
 qexists_tac `1` >>
 subgoal `s'' = s'` >- (
  fs [whileTheory.OLEAST_EQ_SOME]
 ) >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 rpt strip_tac >>
 subgoal `n_l = 0` >- (
  fs []
 ) >>
 fs [weak_exec_n_def, FUNPOW_OPT_compute]
) >>
subgoal `n'' < n'` >- (
 fs []
) >>
QSPECL_X_ASSUM ``!n'. _`` [`n' - n''`] >>
rfs [] >>
subgoal `n' <= n + n''` >- (
 gs [whileTheory.OLEAST_EQ_SOME]
) >>
fs [] >>
QSPECL_X_ASSUM ``!s'''. _`` [`s''`] >>
(* Should be possible to prove with some inter theorem... *)
subgoal `m.weak s'' ls1 s'` >- (
 (* Next state in s'' is s'... *)
 PAT_ASSUM ``weak_model m`` (fn thm => simp [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 qexists_tac `n' - n''` >>
 fs [] >>
 rpt conj_tac >| [
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'`, `s`] >>
  fs [whileTheory.OLEAST_EQ_SOME],

  metis_tac [weak_pc_in_thm],

  rpt strip_tac >>
  fs [whileTheory.OLEAST_EQ_SOME] >>
  PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
  (* TODO: Make some kind of lemma here? *)
  subgoal `n'''' = n'` >- (
   Cases_on `n' < n'4'` >- (
    QSPECL_X_ASSUM ``!n'.
           n' < n'4' /\ n' > 0 ==>
           ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'`] >>
    gs []
   ) >>
   Cases_on `n' > n'4'` >- (
    QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT m.trs n'' s <> SOME s'`` [`n''''`] >>
    gs []
   ) >>
   fs []
  ) >>
  gs [] >>
  QSPECL_X_ASSUM ``!n'5'.
          n'5' < n' /\ n'5' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n'5' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n''' + n''`] >>
  gs [] >>
  qexists_tac `ms''` >>
  fs [] >>
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'' + n'3'`, `s`] >>
  fs []
 ]
) >>
fs [] >>
subgoal `(OLEAST n'. FUNPOW_OPT m.trs n' s'' = SOME s') = SOME (n' - n'')` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 conj_tac >| [
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'`, `s`] >>
  fs [],

  rpt strip_tac >>
  QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT m.trs n'' s <> SOME s'`` [`n'' + n'''`] >>
  gs [] >>
  metis_tac [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM]
 ]
) >>
fs [] >>
subgoal `s'' <> s'` >- (
 (* Since s'' NOTIN ls1, while s' IN ls1 *)
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'3' = n'` (fn thm => fs [thm]) >- (
  Cases_on `n' < n'3'` >- (
   QSPECL_X_ASSUM ``!n'.
          n' < n'3' /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'`] >>
   gs [whileTheory.OLEAST_EQ_SOME]
  ) >>
  Cases_on `n' > n'3'` >- (
   gs [whileTheory.OLEAST_EQ_SOME]
  ) >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!n'5'.
          n'5' < n' /\ n'5' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n'5' s = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n''`] >>
 gs [whileTheory.OLEAST_EQ_SOME] >>
 strip_tac >>
 fs []
) >>
fs [] >>
qexists_tac `1 + n_l` >>
fs [] >>
irule weak_exec_n_OLEAST_inter >>
fs [] >>
qexistsl_tac [`n''`, `s''`] >>
fs []
QED

(* TODO: Generalise this *)
(* TODO: Change weak_exec_n 1 to weak? *)
Theorem weak_exec_1_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'.
 weak_exec_n m ms ls1 1 = SOME ms' ==>
 ms <> ms' ==>
 ls1 SUBSET ls2 ==>
 ?n. n >= 1 /\ (OLEAST n. weak_exec_n m ms ls2 n = SOME ms') = SOME n
Proof
rpt strip_tac >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_to_n thm)]) >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
subgoal `?n'. n' > 0 /\ (OLEAST n'. FUNPOW_OPT m.trs n' ms = SOME ms') = SOME n'` >- (
 (* Since weak goes from ms to ms', there must be a least number of primitive transitions such that
  * ms goes to ms' *)
 metis_tac [weak_least_trs]
) >>
irule weak_exec_1_superset_lemma >>
fs [] >>
rpt strip_tac >| [
 qexists_tac `n'` >>
 fs [],

 metis_tac []
]
QED

(* TODO: Strengthen conclusion to state either ms'' is ms', or pc is in ls2? *)
Theorem weak_exec_exists_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'. 
 m.weak ms ls1 ms' ==>
 ?ms''. weak_exec m (ls1 UNION ls2) ms = SOME ms''
Proof
rpt strip_tac >>
fs [weak_exec_def, weak_nonempty] >>
metis_tac [weak_superset_thm]
QED

(* Note: ms <> ms' used to avoid proving case where least n is zero *)
Theorem weak_exec_n_exists_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms'. 
 m.weak ms ls1 ms' ==>
 ms <> ms' ==>
 ?n. (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n
Proof
rpt strip_tac >>
fs [whileTheory.OLEAST_EQ_SOME] >>
subgoal `weak_exec_n m ms ls1 1 = SOME ms'` >- (
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_exec_exists thm]) >>
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_exec_to_n thm])
) >>
imp_res_tac weak_exec_1_superset >>
QSPECL_X_ASSUM ``!ls2. _`` [`ls1 UNION ls2`] >>
fs [] >>
qexists_tac `n` >>
fs [whileTheory.OLEAST_EQ_SOME]
QED

Theorem weak_exec_least_nonzero:
 !m.
 weak_model m ==>
 !ms ls ms' n_l.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 ms <> ms' ==>
 n_l > 0
Proof
rpt strip_tac >>
Cases_on `n_l` >> (
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def, FUNPOW_OPT_def]
QED

Theorem weak_exec_sing_least_less:
 !m.
 weak_model m ==>
 !ms ls ms' n_l.
 SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms') ==>
 ?n_l'. (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l' /\ n_l' < n_l
Proof
rpt strip_tac >>
fs [pred_setTheory.SING_DEF, whileTheory.OLEAST_EQ_SOME] >>
qexists_tac `x` >>
rpt strip_tac >> (
 fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING]
) >>
QSPECL_X_ASSUM ``!y. y < n_l /\ weak_exec_n m ms ls y = SOME ms' ==> x = y`` [`n`] >>
gs []
QED


(* TODO: Technically, this doesn't need OLEAST for the encounter of ms' *)
Theorem weak_exec_incr_least:
 !m.
 weak_model m ==>
 !ms ls ms' ms_e n_l n_l' ms''.
 (OLEAST n. weak_exec_n m ms ls n = SOME ms_e) = SOME n_l ==>
 ms'' <> ms_e ==>
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l' ==>
 m.weak ms' ls ms'' ==>
 SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms'') ==>
 n_l' < n_l ==>
 (OLEAST n. weak_exec_n m ms ls n = SOME ms'') = SOME (SUC n_l')
Proof
rpt strip_tac >>
imp_res_tac weak_exec_incr_last >>
fs [whileTheory.OLEAST_EQ_SOME] >>
rpt strip_tac >>
subgoal `SUC n_l' < n_l` >- (
 Cases_on `SUC n_l' = n_l` >- (
  fs []
 ) >>
 fs []
) >>
fs [pred_setTheory.SING_DEF] >>
fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING] >>
QSPECL_ASSUM ``!y. y < n_l /\ weak_exec_n m ms ls y = SOME ms'' ==> x = y`` [`SUC n_l'`] >>
QSPECL_X_ASSUM ``!y. y < n_l /\ weak_exec_n m ms ls y = SOME ms'' ==> x = y`` [`n`] >>
gs []
(* Due to SING (\n. n < n_l /\ weak_exec_n m ms ls n = SOME ms''),
 * both weak_exec_n m ms ls (SUC n_l') and weak_exec_n m ms ls n
 * can't lead to ms''. NOTE: Requires SUC n_l' < n_l *)
(* OK: If ms' was first encountered at n_l' weak iterations to ls, and
 * if one additional weak transition to ls goes to ms'', then if
 * ms'' is uniquely encountered before n_l weak transitions to ls and n_l
 * is greater than n_l', then SUC n_l' must be the least number of weak transitions
 * needed to reach ms'' *)
QED

Theorem weak_exec_uniqueness_alt:
 !m.
 weak_model m ==>
 !ms ls ms' ms'' ms''' n_l n_l'. 
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 (OLEAST n. weak_exec_n m ms ls n = SOME ms'') = SOME n_l' ==>
 n_l' < n_l ==>
 m.weak ms'' ls ms''' ==>
 ms''' <> ms' ==>
 SING (\n_l''. n_l'' < n_l /\ weak_exec_n m ms ls n_l'' = SOME ms''')
Proof
rpt strip_tac >>
subgoal `weak_exec_n m ms ls (n_l' + 1) = SOME ms'3'` >- (
 irule weak_exec_n_add >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_exec_exists, weak_exec_to_n]
) >>
(* Suppose there exists some earlier encounter of ms''' *)
Cases_on `?n_l''. n_l'' < (n_l' + 1) /\ weak_exec_n m ms ls n_l'' = SOME ms'''` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `weak_exec_n m ms''' ls (n_l - (n_l' + 1)) = SOME ms'` >- (
  irule weak_exec_n_split2 >>
  fs [] >>
  qexists_tac `ms` >>
  fs []
 ) >>
 subgoal `weak_exec_n m ms ls (n_l'' + (n_l - (n_l' + 1))) = SOME ms'` >- (
  irule weak_exec_n_add >>
  fs [] >>
  qexists_tac `ms'3'` >>
  fs []
 ) >>
 QSPECL_ASSUM ``!n. n < n_l ==> weak_exec_n m ms ls n <> SOME ms'`` [`(n_l'' + (n_l - (n_l' + 1)))`] >>
 gs []
) >>
fs [] >>
(* If there were no earlier encounter of ms''', then the first encounter was at n_l' + 1 *)
subgoal `(OLEAST n_l. weak_exec_n m ms ls n_l = SOME ms''') = SOME (n_l' + 1)` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac []
) >>

(* Suppose there exists some later encounter of ms''' *)
Cases_on `?n_l''. n_l'' > (n_l' + 1) /\ n_l'' < n_l /\ weak_exec_n m ms ls n_l'' = SOME ms'''` >- (
 fs [] >>
 subgoal `(OLEAST n_l. weak_exec_n m ms''' ls n_l = SOME ms') = SOME (n_l - (n_l' + 1))` >- (
  fs [whileTheory.OLEAST_EQ_SOME] >>
  rpt strip_tac >| [
   irule weak_exec_n_split2 >>
   fs [] >>
   qexists_tac `ms` >>
   fs [],

   (* TODO: Prove the OLEAST part... *)
   subgoal `weak_exec_n m ms ls ((n_l' + 1) + n_l'3') <> SOME ms'` >- (
    QSPECL_ASSUM ``!n. n < n_l ==> weak_exec_n m ms ls n <> SOME ms'`` [`(n_l' + 1) + n_l'3'`] >>
    gs []
   ) >>
   subgoal `weak_exec_n m ms ls ((n_l' + 1) + n_l'3') = SOME ms'` >- (
    irule weak_exec_n_add >>
    fs []
   )
  ]
 ) >>
 subgoal `weak_exec_n m ms''' ls (n_l'' - (n_l' + 1)) = SOME ms'''` >- (
  irule weak_exec_n_split2 >>
  fs [] >>
  qexists_tac `ms` >>
  fs []
 ) >>
 (* By weak_exec_n_cycle *)
 subgoal `(n_l - (n_l' + 1)) < (n_l'' - (n_l' + 1))` >- (
  irule weak_exec_n_cycle_alt >>
  fs [] >>
  qexistsl_tac [`ls`, `m`, `ms'''`, `ms'`] >>
  gs [whileTheory.OLEAST_EQ_SOME]
 ) >>
 gs []
) >>
fs [] >>
gs [pred_setTheory.SING_DEF, GSYM pred_setTheory.UNIQUE_MEMBER_SING] >>
qexists_tac `n_l' + 1` >>
rpt strip_tac >| [
 Cases_on `n_l' + 1 = n_l` >- (
  gvs [whileTheory.OLEAST_EQ_SOME]
 ) >>
 gs [],

 irule weak_exec_n_add >>
 fs [] >>
 qexists_tac `ms''` >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_exec_exists, weak_exec_to_n],

 res_tac >>
 gs [arithmeticTheory.EQ_LESS_EQ, arithmeticTheory.NOT_LESS]
]
QED

Theorem weak_exec_unique_start:
 !m.
 weak_model m ==>
 !ms ls ms' n_l. 
 (OLEAST n. weak_exec_n m ms ls n = SOME ms') = SOME n_l ==>
 ms <> ms' ==>
 SING (\n_l'. n_l' < n_l /\ weak_exec_n m ms ls n_l' = SOME ms)
Proof
rpt strip_tac >>
gs [pred_setTheory.SING_DEF, GSYM pred_setTheory.UNIQUE_MEMBER_SING] >>
qexists_tac `0` >>
rpt strip_tac >| [
 Cases_on `n_l = 0` >> (
  fs [weak_exec_n_def, FUNPOW_OPT_compute, whileTheory.OLEAST_EQ_SOME]
 ),

 fs [weak_exec_n_def, FUNPOW_OPT_compute],

 Cases_on `y > 0` >- (
  imp_res_tac weak_exec_n_cycle_alt >>
  fs []
 ) >>
 fs []
]
QED

(* Uses the fact that exit labels are disjoint from loop point to know that
 * we have not yet exited the loop after another weak transition, i.e. the
 * number of loops is still less than n_l *)
Theorem weak_exec_less_incr_superset:
 !m.
 weak_model m ==>
 !ms ls1 ls2 ms' ms'' ms''' n_l n_l'.
 DISJOINT ls1 ls2 ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms') = SOME n_l ==>
 m.pc ms' IN ls2 ==>
 (OLEAST n. weak_exec_n m ms (ls1 UNION ls2) n = SOME ms'') = SOME n_l' ==>
 n_l' < n_l ==>
 m.weak ms'' (ls1 UNION ls2) ms''' ==>
 m.pc ms''' NOTIN ls2 ==>
 SUC n_l' < n_l
Proof
rpt strip_tac >>
Cases_on `SUC n_l' = n_l` >- (
 subgoal `ms''' = ms'` >- (
  subgoal `weak_exec_n m ms (ls1 UNION ls2) (SUC n_l') = SOME ms'''` >- (
   metis_tac [weak_exec_incr_last]
  ) >>
  gs [whileTheory.OLEAST_EQ_SOME]
 ) >>
 fs []
) >>
fs []
QED


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
  irule weak_exec_uniqueness_alt >>
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
