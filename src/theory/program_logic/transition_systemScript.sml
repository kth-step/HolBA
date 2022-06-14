open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

val _ = new_theory "transition_system";

(* Transition system *)
Datatype:
 transition_system_t =
  <|(* Transition function *)
    trs : 'a -> 'a option;
    (* Weak transition relation *)
    weak : ('b -> bool) -> 'a -> 'a -> bool;
    (* A function to obtain the control state from a state.
     * This allows for isolating parts of the state that
     * the weak transition is provably oblivious to. *)
    ctrl : 'a -> 'b
   |>
End

(* A weak transition in a transition system is first-encounter
 * if this property is fulfilled. *)
Definition first_enc_def:
 first_enc TS =
  !s ls s'. TS.weak ls s s' =
   ?n.
    (n > 0 /\
     FUNPOW_OPT TS.trs n s = SOME s' /\
     TS.ctrl s' IN ls
    ) /\
    !n'.
     n' < n /\ n' > 0 ==>
     ?s''.
      FUNPOW_OPT TS.trs n' s = SOME s'' /\
      TS.ctrl s'' NOTIN ls
End

(* Avoids expanding first_enc_def, but rewrites all weak using
 * the first_enc assumption without deleting it *)
val first_enc_weak_tac =
 PAT_ASSUM ``first_enc TS`` (fn thm => fs [MP (fst $ EQ_IMP_RULE (Q.SPEC `TS` first_enc_def)) thm]);
val first_enc_weak_goal_tac =
 PAT_ASSUM ``first_enc TS`` (fn thm => simp [MP (fst $ EQ_IMP_RULE (Q.SPEC `TS` first_enc_def)) thm]);

Theorem weak_comp:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s' s''.
   TS.weak (ls1 UNION ls2) s s' ==>
   TS.ctrl s' NOTIN ls2 ==>
   TS.weak ls2 s' s'' ==>
   TS.weak ls2 s s''
Proof
rpt strip_tac >>
first_enc_weak_tac >>
qexists_tac `n' + n` >>
gs [] >>
rpt strip_tac >| [
 metis_tac [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM],

 subgoal `?s''. FUNPOW_OPT TS.trs (n''-n) s' = SOME s''` >- (
  irule FUNPOW_OPT_prev_EXISTS >>
  qexistsl_tac [`n'`, `s''`] >>
  fs []
 ) >>
 Cases_on `n'' < n` >- (
  metis_tac [pred_setTheory.IN_UNION]
 ) >>
 Cases_on `n'' = n` >- (
  metis_tac []
 ) >>
 qexists_tac `s'''` >>
 conj_tac >| [
  subgoal `n'' > n` >- (
   fs []
  ) >>
  imp_res_tac FUNPOW_OPT_ADD_thm >>
  gs [arithmeticTheory.SUB_ADD, arithmeticTheory.GREATER_DEF],

  QSPECL_X_ASSUM ``!n'':num. n'' < n' /\ n'' > 0 ==> _`` [`n''-n`] >>
  gs []
 ]
]
QED

Theorem weak_unique:
 !TS.
  first_enc TS ==>
  !ls s s' s''.
   TS.weak ls s s' ==>
   TS.weak ls s s'' ==>
   s' = s''
Proof
rpt strip_tac >>
first_enc_weak_tac >>
`n = n'` suffices_by (
 strip_tac >>
 fs []
) >>
Cases_on `n < n'` >- (
 QSPECL_X_ASSUM ``!n'':num. n'' < n' /\ n'' > 0 ==> _`` [`n`] >>
 rfs []
) >>
Cases_on `n > n'` >- (
 QSPECL_X_ASSUM ``!n'':num. n'' < n /\ n'' > 0 ==> _`` [`n'`] >>
 rfs [] 
) >>
fs [] 
QED

Theorem weak_union:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   TS.weak (ls1 UNION ls2) s s' ==>
   TS.ctrl s' NOTIN ls1 ==>
   TS.weak ls2 s s'
Proof
rpt strip_tac >>
first_enc_weak_tac >>
qexists_tac `n` >>
metis_tac [pred_setTheory.IN_UNION]
QED

Theorem weak_union2:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   TS.weak (ls1 UNION ls2) s s' ==>
   TS.ctrl s' IN ls2 ==>
   TS.weak ls2 s s'
Proof
rpt strip_tac >>
first_enc_weak_tac >>
qexists_tac `n` >>
metis_tac [pred_setTheory.IN_UNION]
QED

Theorem weak_ctrl_in:
 !TS.
  first_enc TS ==>
  !ls s s'.
   TS.weak ls s s' ==>
   TS.ctrl s' IN ls
Proof
metis_tac [first_enc_def]
QED

Theorem weak_union_ctrl_not_in:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   TS.weak (ls1 UNION ls2) s s' ==>
   TS.ctrl s' NOTIN ls2 ==>
   TS.weak ls1 s s'
Proof
rpt strip_tac >>
first_enc_weak_tac >>
metis_tac [pred_setTheory.IN_UNION]
QED

Definition ominus_def:
 (ominus NONE _ = NONE) /\
 (ominus _ NONE = NONE) /\
 (ominus (SOME (n:num)) (SOME n') = SOME (n - n'))
End

Theorem weak_superset_thm:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   TS.weak ls1 s s' ==>
   ?s''. TS.weak (ls1 UNION ls2) s s''
Proof
rpt strip_tac >>
first_enc_weak_tac >>
Cases_on `(OLEAST n'. ?s''. n' > 0 /\ n' < n /\ FUNPOW_OPT TS.trs n' s = SOME s'' /\ TS.ctrl s'' IN ls2)` >- (
 fs [] >>
 qexistsl_tac [`s'`, `n`] >>
 fs [] >>
 rpt strip_tac >>
 fs [whileTheory.OLEAST_EQ_NONE] >>
 metis_tac []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
qexistsl_tac [`s''`, `x`] >>
fs [] >>
rpt strip_tac >>
QSPECL_X_ASSUM  ``!n':num. n' < n /\ n' > 0 ==> _`` [`n''`] >>
gs [] >>
QSPECL_X_ASSUM  ``!n':num. n' < x ==> _`` [`n''`] >>
gs []
QED

Theorem weak_nonempty:
 !TS.
  first_enc TS ==>
  !s ls. 
   TS.weak ls s <> {} <=> (?s'. TS.weak ls s s')
Proof
rpt strip_tac >>
fs [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
eq_tac >> (rpt strip_tac) >| [
 qexists_tac `x` >>
 fs [pred_setTheory.IN_APP],

 qexists_tac `s'` >>
 fs [pred_setTheory.IN_APP]
]
QED

Theorem weak_inter:
 !TS.
  first_enc TS ==>
  !s s' s'' ls1 ls2.
   DISJOINT ls1 ls2 ==>
   TS.weak ls2 s s' ==>
   TS.weak (ls1 UNION ls2) s s'' ==>
   TS.ctrl s'' IN ls1 ==>
   TS.weak ls2 s'' s'
Proof
rpt strip_tac >>
(* s goes to s' in n steps. s goes to s'' in n' steps, for which:
 * n'>n: impossible, by the first-encounter property
 * n=n': impossible, since s' is in ls2 and s'' is in ls1 (disjoint sets)
 * n'<n: then s' can be reached by taking n'-n steps, with no ls2-encounters
 * in-between *)
first_enc_weak_tac >>
subgoal `~(n'>n)` >- (
 QSPECL_X_ASSUM ``!n'':num. n'' < n' /\ n'' > 0 ==> _`` [`n`] >>
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
 qexists_tac `s` >>
 fs [],

 (* non-encounter in earlier steps *)
 QSPECL_X_ASSUM ``!n':num. n' < n /\ n' > 0 ==> _`` [`n' + n''`] >>
 gs [] >>
 qexists_tac `s'''` >>
 fs [] >>
 metis_tac [FUNPOW_OPT_INTER, arithmeticTheory.ADD_COMM]
]
QED

Theorem weak_least_trs:
 !TS.
  first_enc TS ==>
  !s ls s'.
   s <> s' ==>
   TS.weak ls s s' ==>
   ?n'. n' > 0 /\ (OLEAST n'. FUNPOW_OPT TS.trs n' s = SOME s') = SOME n'
Proof
rpt strip_tac >>
first_enc_weak_tac >>
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

Theorem weak_union_ctrl:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s' s''.
   TS.weak ls2 s s' ==>
   TS.weak (ls1 UNION ls2) s s'' ==>
   s' <> s'' ==>
   TS.ctrl s'' IN ls1
Proof
rpt strip_tac >>
first_enc_weak_tac >>
Cases_on `n' > n` >- (
 QSPECL_X_ASSUM ``!n'':num. n'' < n' /\ n'' > 0 ==> _`` [`n`] >>
 gs []
) >>
Cases_on `n' = n` >- (
 gs []
) >>
QSPECL_X_ASSUM ``!n':num. n' < n /\ n' > 0 ==> _`` [`n'`] >>
gs []
QED

Theorem weak_subset:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   TS.weak (ls1 UNION ls2) s s' ==>
   ls1 SUBSET ls2 ==>
   TS.weak ls2 s s'
Proof
rpt strip_tac >>
fs [pred_setTheory.SUBSET_UNION_ABSORPTION]
QED


(****************************)
(* Weak transition function *)
(****************************)

(* This is a non-executable function that computes a state (Hilbert's choice of one)
 * that is related to the given initial state by weak to ls. *)
Definition weak_exec_def:
 weak_exec TS ls s =
  let
   S' = TS.weak ls s
  in
   if S' = {}
   then NONE
   else SOME (CHOICE S')
End

(* The above, applied multiple times *)
Definition weak_exec_n_def:
 weak_exec_n TS s ls n = FUNPOW_OPT (weak_exec TS ls) n s
End

Theorem weak_exec_exists:
 !TS.
  first_enc TS ==>
  !ls s s'.
  TS.weak ls s s' <=> weak_exec TS ls s = SOME s'
Proof
rpt strip_tac >>
fs [weak_exec_def] >>
eq_tac >> (
 strip_tac
) >| [
 subgoal `TS.weak ls s = {s'}` >- (
  fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING, pred_setTheory.IN_APP] >>
  metis_tac [weak_unique]
 ) >>
 fs [],

 metis_tac [pred_setTheory.CHOICE_DEF, pred_setTheory.IN_APP]
]
QED

(* TODO: Replace weak with weak_exec_n of 1 in the below? *)

Theorem weak_exec_to_n:
  !TS ls s s'. 
   weak_exec TS ls s = SOME s' <=>
   weak_exec_n TS s ls 1 = SOME s'
Proof
rpt strip_tac >>
fs [weak_exec_n_def, FUNPOW_OPT_def]
QED

Theorem weak_exec_n_prev:
 !TS ls s s' n_l.
  weak_exec_n TS s ls (SUC n_l) = SOME s' ==>
  ?s''. weak_exec_n TS s ls n_l = SOME s'' /\ weak_exec_n TS s'' ls 1 = SOME s'
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
qexistsl_tac [`SUC n_l`, `s`] >>
fs [arithmeticTheory.ADD1]
QED

(* TODO: Useful?
Theorem weak_exec_n_split:
!m. first_enc m ==>
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
 !TS ls s s' s'' n n'.
   n >= n' ==>
   weak_exec_n TS s ls n' = SOME s'' ==>
   weak_exec_n TS s ls n = SOME s' ==>
   weak_exec_n TS s'' ls (n - n') = SOME s'
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


Theorem weak_exec_n_cycle:
 !TS s s' ls n_l n_l'.
 n_l > 0 /\ weak_exec_n TS s ls n_l = SOME s ==>
 s <> s' ==>
 (OLEAST n_l'. weak_exec_n TS s ls n_l' = SOME s') = SOME n_l' ==>
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
subgoal `weak_exec_n TS s ls (n_l' - n_l) = SOME s'` >- (
 irule weak_exec_n_split2 >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `s` >>
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
QSPECL_X_ASSUM ``!n_l''. n_l'' < n_l' ==> weak_exec_n TS s ls n_l'' <> SOME s'`` [`n_l' - n_l`] >>
gs []
QED

(* TODO: Technically, this doesn't need OLEAST for the encounter of s'
 * Let this rely on sub-lemma for incrementing weak_exec_n instead
 * of reasoning on FUNPOW_OPT *)
Theorem weak_exec_incr_last:
 !TS.
 first_enc TS ==>
 !s ls s' n_l s''.
 (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l ==>
 TS.weak ls s' s'' ==>
 weak_exec_n TS s ls (SUC n_l) = SOME s''
Proof
rpt strip_tac >>
simp [weak_exec_n_def, arithmeticTheory.ADD1] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
irule FUNPOW_OPT_ADD_thm >>
qexists_tac `s'` >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def] >>
simp [FUNPOW_OPT_def] >>
metis_tac [weak_exec_exists]
QED

Theorem weak_exec_incr_first:
 !TS.
 first_enc TS ==>
 !s ls s' n_l s''.
 TS.weak ls s s' ==>
 (OLEAST n. weak_exec_n TS s' ls n = SOME s'') = SOME n_l ==>
 weak_exec_n TS s ls (SUC n_l) = SOME s''
Proof
rpt strip_tac >>
simp [weak_exec_n_def, arithmeticTheory.ADD1] >>
irule FUNPOW_OPT_ADD_thm >>
qexists_tac `s'` >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def] >>
simp [FUNPOW_OPT_def] >>
metis_tac [weak_exec_exists]
QED

Theorem weak_exec_n_add:
 !TS s s' s'' ls n n'.
 weak_exec_n TS s ls n = SOME s' ==>
 weak_exec_n TS s' ls n' = SOME s'' ==>
 weak_exec_n TS s ls (n + n') = SOME s''
Proof
rpt strip_tac >>
fs [weak_exec_n_def] >>
metis_tac [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM]
QED

Theorem weak_exec_n_inter:
 !TS.
 first_enc TS ==>
 !s s' ls1 ls2 n_l n_l'.
 DISJOINT ls1 ls2 ==>
 weak_exec_n TS s ls2 1 = SOME s' ==>
 (OLEAST n_l. weak_exec_n TS s (ls1 UNION ls2) n_l = SOME s') = SOME n_l ==>
 n_l' < n_l ==>
 !s''.
 (OLEAST n_l. weak_exec_n TS s (ls1 UNION ls2) n_l = SOME s'') = SOME n_l' ==>
 weak_exec_n TS s'' ls2 1 = SOME s'
Proof
ntac 7 strip_tac >>
Induct_on `n_l'` >- (
 rpt strip_tac >>
 fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def, FUNPOW_OPT_compute]
) >>
rpt strip_tac >>
gs [whileTheory.OLEAST_EQ_SOME] >>
imp_res_tac weak_exec_n_prev >>
QSPECL_X_ASSUM ``!s'3'.
          weak_exec_n TS s (ls1 UNION ls2) n_l' = SOME s'3' /\
          (!n_l.
             n_l < n_l' ==>
             weak_exec_n TS s (ls1 UNION ls2) n_l <> SOME s'3') ==>
          weak_exec_n TS s'3' ls2 1 = SOME s'`` [`s'''`] >>
gs [] >>
subgoal `!n_l. n_l < n_l' ==> weak_exec_n TS s (ls1 UNION ls2) n_l <> SOME s'3'` >- (
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n_l.
          n_l < SUC n_l' ==>
          weak_exec_n TS s (ls1 UNION ls2) n_l <> SOME s''`` [`SUC n_l''`] >>
 gs [] >>
 metis_tac [weak_exec_n_add, arithmeticTheory.ADD1]
) >>
fs [GSYM weak_exec_to_n] >>
PAT_ASSUM ``first_enc TS`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
irule weak_inter >>
fs [] >>
qexistsl_tac [`ls1`, `s'''`] >>
fs [] >>
subgoal `s' <> s''` >- (
QSPECL_X_ASSUM ``!n_l'.
          n_l' < n_l ==> weak_exec_n TS s (ls1 UNION ls2) n_l' <> SOME s'`` [`SUC n_l'`] >>
 gs []
) >>
metis_tac [weak_union_ctrl]
QED

Theorem weak_inter_exec:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s n_l s' s''.
   TS.weak ls2 s s' ==>
   DISJOINT ls1 ls2 ==>
   (OLEAST n. weak_exec_n TS s (ls1 UNION ls2) n = SOME s') = SOME n_l ==>
   SING (\n. n < n_l /\ weak_exec_n TS s (ls1 UNION ls2) n = SOME s'') ==>
   TS.weak ls2 s'' s'
Proof
rpt strip_tac >>
PAT_ASSUM ``first_enc TS`` (fn thm => fs [HO_MATCH_MP weak_exec_exists thm]) >>
fs [weak_exec_to_n] >>
irule weak_exec_n_inter >>
fs [pred_setTheory.SING_DEF, whileTheory.OLEAST_EQ_SOME] >>
fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING] >>
qexistsl_tac [`ls1`, `n_l`, `x`, `s`] >>
fs [] >>
rpt strip_tac >>
QSPECL_X_ASSUM  ``!y. y < n_l /\ weak_exec_n TS s (ls1 UNION ls2) y = SOME s'' ==> x = y`` [`n_l'`] >>
subgoal `n_l' < n_l` >- (
 gs []
) >>
fs []
QED

Theorem weak_exec_n_OLEAST_equiv:
 !TS.
  first_enc TS ==>
  !ls s s'.
   (OLEAST n_l. n_l > 0 /\ weak_exec_n TS s ls n_l = SOME s') = SOME 1 ==>
   TS.weak ls s s'
Proof
rpt strip_tac >>
fs [whileTheory.OLEAST_EQ_SOME, GSYM weak_exec_to_n] >>
PAT_ASSUM ``first_enc TS`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)])
QED

(* Continuing weak_exec_n at s'', intermediately between s and s'' *)
Theorem weak_exec_n_OLEAST_inter:
 !TS.
  first_enc TS ==>
  !s s' s'' ls n' n'' n_l.
  (OLEAST n'. FUNPOW_OPT TS.trs n' s = SOME s') = SOME n' ==>
  (OLEAST n''. n'' > 0 /\ FUNPOW_OPT TS.trs n'' s = SOME s'') = SOME n'' ==>
  n' > n'' ==>
  (OLEAST n_l. n_l > 0 /\ weak_exec_n TS s ls n_l = SOME s'') = SOME 1 ==>
  (OLEAST n_l. weak_exec_n TS s'' ls n_l = SOME s') = SOME n_l ==>
  (OLEAST n_l. weak_exec_n TS s ls n_l = SOME s') = SOME (n_l + 1)
Proof
rpt strip_tac >>
simp [whileTheory.OLEAST_EQ_SOME] >>
conj_tac >| [
 metis_tac [arithmeticTheory.ADD1, weak_exec_incr_first, weak_exec_n_OLEAST_equiv],

 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `s <> s'` >- (
  QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT TS.trs n'' s <> SOME s'`` [`0`] >>
  subgoal `0 < n'` >- (
   fs []
  ) >>
  gs [FUNPOW_OPT_compute]
 ) >>
 subgoal `s'' <> s'` >- (
  QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT TS.trs n'' s <> SOME s'`` [`n''`] >>
  gs []
 ) >>
 subgoal `n_l > 0` >- (
  Cases_on `n_l = 0` >- (
   fs [weak_exec_n_def, FUNPOW_OPT_compute]
  ) >>
  fs []
 ) >>
 `weak_exec_n TS s ls 1 <> SOME s' /\ !n_l'. n_l' < n_l ==> weak_exec_n TS s'' ls n_l' <> SOME s'` suffices_by (
  rpt strip_tac >>
  fs [] >>
  QSPECL_X_ASSUM ``!n_l'. n_l' < n_l ==> weak_exec_n TS s'' ls n_l' <> SOME s'`` [`n_l' - 1`] >>
  gs [] >>
  subgoal `n_l' >= 1` >- (
   Cases_on `n_l' = 0` >- (
    fs [weak_exec_n_def, FUNPOW_OPT_compute]
   ) >>
   fs []
  ) >>
  metis_tac [weak_exec_n_split2]
 ) >>
 QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT TS.trs n'' s <> SOME s'`` [`n''`] >>
 gs [] 
]
QED

Theorem weak_exec_1_superset_lemma:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s'.
   !n n'. n' <= n ==>
          n' >= 1 ==>
          !s. TS.weak ls1 s s' /\ ((OLEAST n'. FUNPOW_OPT TS.trs n' s = SOME s') = SOME n') ==>
          s <> s' ==>
          ls1 SUBSET ls2 ==>
          ?n_l. n_l >= 1 /\ (OLEAST n_l. weak_exec_n TS s ls2 n_l = SOME s') = SOME n_l
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
  fs [GSYM weak_exec_to_n] >>
  PAT_ASSUM ``first_enc TS`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
  first_enc_weak_tac >>
  qexists_tac `1` >>
  fs [] >>
  metis_tac [weak_ctrl_in, pred_setTheory.SUBSET_THM],

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
subgoal `?s''. (OLEAST n_l''. n_l'' > 0 /\ weak_exec_n TS s ls2 n_l'' = SOME s'') = SOME 1` >- (
 subgoal `?s''. TS.weak (ls1 UNION ls2) s s''` >- (
  metis_tac [weak_superset_thm]
 ) >>
 qexistsl_tac [`s''`] >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_subset, weak_exec_to_n, weak_exec_exists]
) >>
subgoal `?n''. (OLEAST n''. n'' > 0 /\ FUNPOW_OPT TS.trs n'' s = SOME s'') = SOME n''` >- (
 (* Since s'' is reached by non-zero weak transitions, there must be a (least) non-zero number of trs
  * that reaches it *)
 fs [whileTheory.OLEAST_EQ_SOME] >>
 fs [GSYM weak_exec_to_n] >>
 PAT_ASSUM ``first_enc TS`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
 first_enc_weak_tac >>
 qexists_tac `n'''` >>
 fs [] >>
 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n':num. n' < n'3' /\ n' > 0 ==> _`` [`n''''`] >>
 gs []
) >>
(* s'' is reached with more trs than s': contradiction, s' would have been crossed *)
Cases_on `n'' > n'` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `TS.weak ls2 s s''` >- (
  metis_tac [weak_exec_to_n, weak_exec_exists]
 ) >>
 first_enc_weak_tac >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'4' = n''` (fn thm => fs [thm]) >- (
  Cases_on `n'' < n'4'` >- (
   QSPECL_X_ASSUM ``!n':num. n' < n'4' /\ n' > 0 ==> _`` [`n''`] >>
   gs []
  ) >>
  Cases_on `n'' > n'4'` >- (
   QSPECL_X_ASSUM ``!n'3':num. n'3' < n'' ==> _`` [`n''''`] >>
   gs []
  ) >>
  fs []
 ) >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'3' = n'` (fn thm => fs [thm]) >- (
  Cases_on `n' < n'3'` >- (
   QSPECL_X_ASSUM ``!n':num. n' < n'3' /\ n' > 0 ==> _`` [`n'`] >>
   gs []
  ) >>
  Cases_on `n' > n'3'` >- (
   QSPECL_X_ASSUM ``!n':num. n' < n'3' /\ n' > 0 ==> _`` [`n'''`] >>
   gs []
  ) >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!n':num. n' < n'' /\ n' > 0 ==> _`` [`n'`] >>
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
subgoal `TS.weak ls1 s'' s'` >- (
 (* Next state in s'' is s'... *)
 first_enc_weak_goal_tac >>
 qexists_tac `n' - n''` >>
 fs [] >>
 rpt conj_tac >| [
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'`, `s`] >>
  fs [whileTheory.OLEAST_EQ_SOME],

  metis_tac [weak_ctrl_in],

  rpt strip_tac >>
  fs [whileTheory.OLEAST_EQ_SOME] >>
  first_enc_weak_tac >>
  (* TODO: Make some kind of lemma here? *)
  subgoal `n'''' = n'` >- (
   Cases_on `n' < n'4'` >- (
    QSPECL_X_ASSUM ``!n':num. n' < n'4' /\ n' > 0 ==> _`` [`n'`] >>
    gs []
   ) >>
   Cases_on `n' > n'4'` >- (
    QSPECL_X_ASSUM ``!n'':num. n'' < n' ==> _`` [`n''''`] >>
    gs []
   ) >>
   fs []
  ) >>
  gs [] >>
  QSPECL_X_ASSUM ``!n'5':num. n'5' < n' /\ n'5' > 0 ==> _`` [`n''' + n''`] >>
  gs [] >>
  qexists_tac `s'''` >>
  fs [] >>
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'' + n'3'`, `s`] >>
  fs []
 ]
) >>
fs [] >>
subgoal `(OLEAST n'. FUNPOW_OPT TS.trs n' s'' = SOME s') = SOME (n' - n'')` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 conj_tac >| [
  irule FUNPOW_OPT_split >>
  qexistsl_tac [`n'`, `s`] >>
  fs [],

  rpt strip_tac >>
  QSPECL_X_ASSUM ``!n'':num. n'' < n' ==> _`` [`n'' + n'''`] >>
  gs [] >>
  metis_tac [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM]
 ]
) >>
fs [] >>
subgoal `s'' <> s'` >- (
 (* Since s'' NOTIN ls1, while s' IN ls1 *)
 first_enc_weak_tac >>
 (* TODO: Make some kind of lemma here? *)
 Q.SUBGOAL_THEN `n'3' = n'` (fn thm => fs [thm]) >- (
  Cases_on `n' < n'3'` >- (
   QSPECL_X_ASSUM ``!n':num. n' < n'3' /\ n' > 0 ==> _`` [`n'`] >>
   gs [whileTheory.OLEAST_EQ_SOME]
  ) >>
  Cases_on `n' > n'3'` >- (
   gs [whileTheory.OLEAST_EQ_SOME]
  ) >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!n'5':num. n'5' < n' /\ n'5' > 0 ==> _`` [`n''`] >>
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
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'.
   weak_exec_n TS s ls1 1 = SOME s' ==>
   s <> s' ==>
   ls1 SUBSET ls2 ==>
   ?n. n >= 1 /\ (OLEAST n. weak_exec_n TS s ls2 n = SOME s') = SOME n
Proof
rpt strip_tac >>
fs [GSYM weak_exec_to_n] >>
PAT_ASSUM ``first_enc TS`` (fn thm => fs [GSYM (HO_MATCH_MP weak_exec_exists thm)]) >>
subgoal `?n'. n' > 0 /\ (OLEAST n'. FUNPOW_OPT TS.trs n' s = SOME s') = SOME n'` >- (
 (* Since weak goes from s to s', there must be a least number of primitive transitions such that
  * s goes to s' *)
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

(* TODO: Strengthen conclusion to state either s'' is s', or ctrl is in ls2? *)
Theorem weak_exec_exists_superset:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'. 
   TS.weak ls1 s s' ==>
   ?s''. weak_exec TS (ls1 UNION ls2) s = SOME s''
Proof
rpt strip_tac >>
fs [weak_exec_def, weak_nonempty] >>
metis_tac [weak_superset_thm]
QED

(* Note: s <> s' used to avoid proving case where least n is zero *)
Theorem weak_exec_n_exists_superset:
 !TS.
  first_enc TS ==>
  !ls1 ls2 s s'. 
   TS.weak ls1 s s' ==>
   s <> s' ==>
   ?n. (OLEAST n. weak_exec_n TS s (ls1 UNION ls2) n = SOME s') = SOME n
Proof
rpt strip_tac >>
fs [whileTheory.OLEAST_EQ_SOME] >>
subgoal `weak_exec_n TS s ls1 1 = SOME s'` >- (
 PAT_ASSUM ``first_enc TS`` (fn thm => fs [HO_MATCH_MP weak_exec_exists thm]) >>
 fs [weak_exec_to_n]
) >>
imp_res_tac weak_exec_1_superset >>
QSPECL_X_ASSUM ``!ls2. _`` [`ls1 UNION ls2`] >>
fs [] >>
qexists_tac `n` >>
fs [whileTheory.OLEAST_EQ_SOME]
QED

Theorem weak_exec_least_nonzero:
 !TS ls s s' n_l.
 (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l ==>
 s <> s' ==>
 n_l > 0
Proof
rpt strip_tac >>
Cases_on `n_l` >> (
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME, weak_exec_n_def, FUNPOW_OPT_def]
QED

Theorem weak_exec_sing_least_less:
 !TS ls s s' n_l.
 SING (\n. n < n_l /\ weak_exec_n TS s ls n = SOME s') ==>
 ?n_l'. (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l' /\ n_l' < n_l
Proof
rpt strip_tac >>
fs [pred_setTheory.SING_DEF, whileTheory.OLEAST_EQ_SOME] >>
qexists_tac `x` >>
rpt strip_tac >> (
 fs [GSYM pred_setTheory.UNIQUE_MEMBER_SING]
) >>
QSPECL_X_ASSUM ``!y. y < n_l /\ weak_exec_n TS s ls y = SOME s' ==> x = y`` [`n`] >>
gs []
QED


(* TODO: Technically, this doesn't need OLEAST for the encounter of s' *)
Theorem weak_exec_incr_least:
 !TS.
  first_enc TS ==>
  !s ls s' s_e n_l n_l' s''.
   (OLEAST n. weak_exec_n TS s ls n = SOME s_e) = SOME n_l ==>
   s'' <> s_e ==>
   (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l' ==>
   TS.weak ls s' s'' ==>
   SING (\n. n < n_l /\ weak_exec_n TS s ls n = SOME s'') ==>
   n_l' < n_l ==>
   (OLEAST n. weak_exec_n TS s ls n = SOME s'') = SOME (SUC n_l')
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
QSPECL_ASSUM ``!y. y < n_l /\ weak_exec_n TS s ls y = SOME s'' ==> x = y`` [`SUC n_l'`] >>
QSPECL_X_ASSUM ``!y. y < n_l /\ weak_exec_n TS s ls y = SOME s'' ==> x = y`` [`n`] >>
gs []
QED

Theorem weak_exec_uniqueness:
 !TS.
 first_enc TS ==>
 !ls s s' s'' s''' n_l n_l'. 
 (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l ==>
 (OLEAST n. weak_exec_n TS s ls n = SOME s'') = SOME n_l' ==>
 n_l' < n_l ==>
 TS.weak ls s'' s''' ==>
 s''' <> s' ==>
 SING (\n_l''. n_l'' < n_l /\ weak_exec_n TS s ls n_l'' = SOME s''')
Proof
rpt strip_tac >>
subgoal `weak_exec_n TS s ls (n_l' + 1) = SOME s'3'` >- (
 irule weak_exec_n_add >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_exec_exists, weak_exec_to_n]
) >>
(* Suppose there exists some earlier encounter of s''' *)
Cases_on `?n_l''. n_l'' < (n_l' + 1) /\ weak_exec_n TS s ls n_l'' = SOME s'''` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 subgoal `weak_exec_n TS s''' ls (n_l - (n_l' + 1)) = SOME s'` >- (
  irule weak_exec_n_split2 >>
  fs [] >>
  qexists_tac `s` >>
  fs []
 ) >>
 subgoal `weak_exec_n TS s ls (n_l'' + (n_l - (n_l' + 1))) = SOME s'` >- (
  irule weak_exec_n_add >>
  fs [] >>
  qexists_tac `s'3'` >>
  fs []
 ) >>
 QSPECL_ASSUM ``!n. n < n_l ==> weak_exec_n TS s ls n <> SOME s'`` [`(n_l'' + (n_l - (n_l' + 1)))`] >>
 gs []
) >>
fs [] >>
(* If there were no earlier encounter of s''', then the first encounter was at n_l' + 1 *)
subgoal `(OLEAST n_l. weak_exec_n TS s ls n_l = SOME s''') = SOME (n_l' + 1)` >- (
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac []
) >>

(* Suppose there exists some later encounter of s''' *)
Cases_on `?n_l''. n_l'' > (n_l' + 1) /\ n_l'' < n_l /\ weak_exec_n TS s ls n_l'' = SOME s'''` >- (
 fs [] >>
 subgoal `(OLEAST n_l. weak_exec_n TS s''' ls n_l = SOME s') = SOME (n_l - (n_l' + 1))` >- (
  fs [whileTheory.OLEAST_EQ_SOME] >>
  rpt strip_tac >| [
   irule weak_exec_n_split2 >>
   fs [] >>
   qexists_tac `s` >>
   fs [],

   subgoal `weak_exec_n TS s ls ((n_l' + 1) + n_l'3') <> SOME s'` >- (
    QSPECL_ASSUM ``!n. n < n_l ==> weak_exec_n TS s ls n <> SOME s'`` [`(n_l' + 1) + n_l'3'`] >>
    gs []
   ) >>
   subgoal `weak_exec_n TS s ls ((n_l' + 1) + n_l'3') = SOME s'` >- (
    irule weak_exec_n_add >>
    fs []
   )
  ]
 ) >>
 subgoal `weak_exec_n TS s''' ls (n_l'' - (n_l' + 1)) = SOME s'''` >- (
  irule weak_exec_n_split2 >>
  fs [] >>
  qexists_tac `s` >>
  fs []
 ) >>
 (* By weak_exec_n_cycle *)
 subgoal `(n_l - (n_l' + 1)) < (n_l'' - (n_l' + 1))` >- (
  irule weak_exec_n_cycle >>
  fs [] >>
  qexistsl_tac [`TS`, `ls`, `s'''`, `s'`] >>
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
 qexists_tac `s''` >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 metis_tac [weak_exec_exists, weak_exec_to_n],

 res_tac >>
 gs [arithmeticTheory.EQ_LESS_EQ, arithmeticTheory.NOT_LESS]
]
QED

Theorem weak_exec_unique_start:
 !TS.
 first_enc TS ==>
 !s ls s' n_l. 
 (OLEAST n. weak_exec_n TS s ls n = SOME s') = SOME n_l ==>
 s <> s' ==>
 SING (\n_l'. n_l' < n_l /\ weak_exec_n TS s ls n_l' = SOME s)
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
  imp_res_tac weak_exec_n_cycle >>
  fs []
 ) >>
 fs []
]
QED

(* Uses the fact that exit labels are disjoint from loop point to know that
 * we have not yet exited the loop after another weak transition, i.e. the
 * number of loops is still less than n_l *)
Theorem weak_exec_less_incr_superset:
 !TS.
  first_enc TS ==>
   !ls1 ls2 s s' s'' s''' n_l n_l'.
   DISJOINT ls1 ls2 ==>
   (OLEAST n. weak_exec_n TS s (ls1 UNION ls2) n = SOME s') = SOME n_l ==>
   TS.ctrl s' IN ls2 ==>
   (OLEAST n. weak_exec_n TS s (ls1 UNION ls2) n = SOME s'') = SOME n_l' ==>
   n_l' < n_l ==>
   TS.weak (ls1 UNION ls2) s'' s''' ==>
   TS.ctrl s''' NOTIN ls2 ==>
   SUC n_l' < n_l
Proof
rpt strip_tac >>
Cases_on `SUC n_l' = n_l` >- (
 subgoal `s''' = s'` >- (
  subgoal `weak_exec_n TS s (ls1 UNION ls2) (SUC n_l') = SOME s'''` >- (
   metis_tac [weak_exec_incr_last]
  ) >>
  gs [whileTheory.OLEAST_EQ_SOME]
 ) >>
 fs []
) >>
fs []
QED


val _ = export_theory();
