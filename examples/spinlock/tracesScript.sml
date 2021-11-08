open HolKernel Parse boolLib bossLib;

val _ = new_theory "spinlock";

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory;

(*
 * Defintion of traces
 *)

Inductive is_gen_trace:
  (!R s. is_gen_trace R [s]) /\
  (!R s2 s1 t . ((is_gen_trace R (APPEND t [s1])) /\ (R s1 s2)) ==>
                (is_gen_trace R (APPEND t [s1;s2]))
  )
End

Definition gen_traces_def:
  gen_traces R = { t | is_gen_trace R t }
End

Definition parstep_nice_def:
  parstep_nice cid s1 s2 = parstep cid (FST s1) (SND s1) (FST s2) (SND s2)
End

(* memory is monotonic only ever increases, at most by one *)

Theorem parstep_nice_memory_imp:
  !s1 s2. parstep_nice cid s1 s2
  ==> SND s1 = SND s2 \/ ?m. SND s2 = SND s1 ++ [m]
Proof
  fs[par_traces_def,gen_traces_def,parstep_nice_def,pairTheory.FORALL_PROD]
  >> rw[cstep_cases,parstep_cases]
  >> disj2_tac
  >> irule_at Any EQ_REFL
QED

(* set of all traces *)
Definition par_traces_def:
  par_traces = gen_traces (λs1 s2. ?cid. parstep_nice cid s1 s2)
End

Theorem par_traces_ind:
  !P. (!s. P [s])
  /\ (!s2 s1 t. P (t ++ [s1]) /\ (?cid. parstep_nice cid s1 s2) ==> P (t ++ [s1; s2]))
  ==> !tr. tr IN par_traces ==> P tr
Proof
  fs[par_traces_def,gen_traces_def]
  >> ntac 2 strip_tac
  >> `!ps tr. is_gen_trace ps tr ==> ps = (λs1 s2. ?cid. parstep_nice cid s1 s2)
    ==> P tr` by (
    ho_match_mp_tac is_gen_trace_ind
    >> fs[AND_IMP_INTRO,PULL_FORALL,PULL_EXISTS]
  )
  >> fs[PULL_FORALL]
QED

Theorem is_gen_trace_NOT_NULL:
  !R s. is_gen_trace R s ==> ~NULL s
Proof
  ho_match_mp_tac is_gen_trace_ind
  >> fs[NULL_EQ]
QED

Theorem is_gen_trace_EL:
  !R s. is_gen_trace R s ==> !i. SUC i < LENGTH s ==> R (EL i s) (EL (SUC i) s)
Proof
  ho_match_mp_tac is_gen_trace_ind
  >> rw[]
  >> qmatch_assum_rename_tac `SUC i < LENGTH t + 2`
  >> Cases_on `SUC i < LENGTH t`
  >- (
    first_x_assum $ qspec_then `i` mp_tac
    >> fs[EL_APPEND1]
  )
  >> fs[NOT_LESS,LESS_OR_EQ]
  >- (
    `i = LENGTH t` by fs[]
    >> pop_assum $ fs o single
    >> fs[EL_APPEND1,EL_APPEND2]
  )
  >> first_x_assum $ qspec_then `i` mp_tac
  >> fs[EL_APPEND1,EL_APPEND2]
QED

(*
 * well-formed traces and implications of well-formedness
 *)

(* well-formedness of Cores: the cid is unique *)
Definition wf_sys_def:
  wf_sys (sys : core_t -> bool) =
    !cid p st p' st'.
    Core cid p st IN sys /\ Core cid p' st' IN sys
    ==> p = p' /\ st = st'
End

Theorem parstep_nice_wf_sys:
  !s1 s2 cid. wf_sys $ FST s1
  /\ parstep_nice cid s1 s2
  ==> wf_sys $ FST s2
Proof
  `!cid s1 m1 s2 m2. parstep cid s1 m1 s2 m2 ==> wf_sys s1 ==> wf_sys s2` by (
    ho_match_mp_tac parstep_ind
    >> rpt strip_tac
    >> fs[wf_sys_def,AND_IMP_INTRO]
    >> rw[]
    >> first_x_assum dxrule_all >> rw[]
  )
  >> ntac 2 Cases >> fs[parstep_nice_def]
  >> metis_tac[]
QED

Definition empty_prom_def:
  empty_prom s = !cid p st. Core cid p st IN s ==> NULL st.bst_prom
End

(* well-formed traces are certified and thread id's are unique identifiers *)
Definition wf_trace_def:
  wf_trace tr <=> tr IN par_traces /\ wf_sys $ FST $ HD tr
    /\ NULL $ SND $ HD tr /\ empty_prom $ FST $ HD tr
End

Theorem wf_trace_NOT_NULL:
  !tr. wf_trace tr ==> ~NULL tr
Proof
  rw[wf_trace_def,par_traces_def,gen_traces_def]
  >> imp_res_tac is_gen_trace_NOT_NULL
QED

Theorem wf_trace_parstep_EL:
  !tr i. wf_trace tr /\ SUC i < LENGTH tr ==> ?cid. parstep_nice cid (EL i tr) (EL (SUC i) tr)
Proof
  rw[wf_trace_def,par_traces_def,gen_traces_def]
  >> drule is_gen_trace_EL
  >> fs[]
QED

Theorem wf_trace_wf_sys_monotone:
  !tr i. wf_trace tr /\ i < LENGTH tr ==> wf_sys $ FST $ EL i tr
Proof
  `!ps tr. is_gen_trace ps tr ==>
    ps = (λs1 s2. ?cid. parstep_nice cid s1 s2) /\ wf_sys (FST (HD tr)) ==>
     !i. i < LENGTH tr ==> wf_sys (FST (EL i tr))` by (
    ho_match_mp_tac is_gen_trace_ind
    >> rw[]
    >- (qmatch_assum_rename_tac `i < 1` >> Cases_on `i` >> fs[])
    >> qmatch_assum_rename_tac `i < LENGTH t + 2`
    >> Cases_on `NULL t`
    >- (
      fs[NULL_EQ,EL_APPEND1,EL_APPEND2]
      >> fs o single $
        (REWRITE_CONV [GSYM COUNT_LIST_COUNT,GSYM pred_setTheory.IN_COUNT]
        THENC EVAL) ``n < (2 : num)``
      >> drule_all parstep_nice_wf_sys
      >> fs[]
    )
    >> gs[Excl"EL",Excl"EL_restricted",GSYM EL,EL_APPEND1,GSYM LENGTH_NOT_NULL]
    >> Cases_on `i < LENGTH t`
    >- (
      `i < LENGTH t + 1` by fs[]
      >> first_x_assum drule
      >> fs[EL_APPEND1]
    )
    >> gvs[EL_APPEND2,NOT_LESS,LESS_OR_EQ,EL_APPEND1]
    >> first_x_assum $ qspec_then `LENGTH t` mp_tac
    >> fs[EL_APPEND2]
    >> `i = SUC $ LENGTH t` by fs[NOT_LESS,LESS_OR_EQ]
    >> rw[EL_APPEND1]
    >> dxrule_all parstep_nice_wf_sys
    >> fs[]
  )
  >> fs[wf_trace_def,par_traces_def,gen_traces_def]
QED

Theorem wf_trace_wf_sys:
  !tr cid p st p' st' i. wf_trace tr
  /\ Core cid p st IN FST (EL i tr)
  /\ Core cid p' st' IN FST (EL i tr)
  /\ i < LENGTH tr
  ==> p = p' /\ st = st'
Proof
  rpt gen_tac >> strip_tac
  >> dxrule_all $ REWRITE_RULE[wf_sys_def] wf_trace_wf_sys_monotone
  >> fs[]
QED

(* only one core changes in a parstep transition *)

Theorem wf_trace_unchanged:
  !tr p1 p1' p2 p2' cid cid' st1 st1' st2 st2' i prom.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ Core cid p1 st1 IN FST (EL i tr)
  /\ Core cid p1' st1' IN FST (EL (SUC i) tr)
  /\ Core cid' p2 st2 IN FST (EL i tr)
  /\ Core cid' p2' st2' IN FST (EL (SUC i) tr)
  /\ cid <> cid' /\ st1 <> st1'
  ==> p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> drule_all_then assume_tac wf_trace_parstep_EL
  >> gvs[parstep_cases,parstep_nice_def]
  >> Cases_on `cid' = cid''`
  >> gvs[]
  >> drule_then (dxrule_then drule) wf_trace_wf_sys
  >> rw[]
  >> rev_drule_then (dxrule_then drule) wf_trace_wf_sys
  >> rw[]
QED

(* identify the progressing core *)

Theorem parstep_nice_cid_NOT_EQ:
  !cid s1 s2 cid' p p' st st'. parstep_nice cid s1 s2
  /\ Core cid' p st IN FST s1
  /\ Core cid' p' st' IN FST s1
  /\ cid <> cid'
  ==> p = p' /\ st = st'
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,parstep_nice_def,pairTheory.FORALL_PROD]
  >> ho_match_mp_tac parstep_ind
  >> rw[cstep_cases]
  rpt strip_tac >> gvs[progress_def,DISJ_EQ_IMP]
  >> drule_then (dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> drule_then (rev_dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> cheat
QED

(* same core id occurs in next step in the trace *)

Theorem wf_trace_cid_forward1:
  !tr i cid p st. wf_trace tr /\ Core cid p st IN FST (EL i tr)
  /\ SUC i < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL (SUC i) tr)
Proof
  rpt strip_tac
  >> drule_all wf_trace_parstep_EL
  >> rw[parstep_nice_def,parstep_cases]
  >> gvs[]
  >> Cases_on `cid = cid'`
  >> dsimp[]
  >> goal_assum drule
QED

(* same core id occurs later in the trace *)
Theorem wf_trace_cid_forward:
  !j tr i cid p st. wf_trace tr /\ Core cid p st IN FST (EL i tr)
  /\ i <= j /\ j < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL j tr)
Proof
  Induct >> rw[] >> fs[] >- goal_assum drule
  >> dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >- (
    first_x_assum $ drule_then dxrule
    >> rw[]
    >> drule_then irule wf_trace_cid_forward1
    >> rpt $ goal_assum $ drule_at Any
  )
  >> gvs[] >> goal_assum drule
QED

Theorem wf_trace_cid_backward1:
  !i tr cid p st. wf_trace tr /\ Core cid p st IN FST (EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL i tr)
Proof
  rpt strip_tac
  >> drule_all wf_trace_parstep_EL
  >> rw[parstep_nice_def,parstep_cases]
  >> gvs[]
  >> goal_assum drule
QED

Theorem wf_trace_cid_backward:
  !i j tr cid p st. wf_trace tr /\ Core cid p st IN FST (EL j tr)
  /\ i <= j /\ j < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL i tr)
Proof
  ntac 2 gen_tac >> Induct_on `j - i`
  >> rw[] >> fs[PULL_FORALL,AND_IMP_INTRO]
  >- (gvs[LESS_OR_EQ] >- goal_assum drule)
  >> drule_then irule wf_trace_cid_backward1
  >> qpat_x_assum `_ = _ - _:num` $ assume_tac o REWRITE_RULE[SUB_LEFT_EQ]
  >> gvs[]
  >> first_x_assum $ rev_drule_at_then Any irule
  >> goal_assum $ rev_drule_at Any
  >> fs[]
QED

(* a thread id occurs in all states *)
Theorem wf_trace_cid:
  !tr cid p st i j. wf_trace tr /\ Core cid p st IN FST (EL i tr)
  /\ i < LENGTH tr /\ j < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL j tr)
Proof
  rw[]
  >> Cases_on `i <= j`
  >- (
    drule_then irule wf_trace_cid_forward
    >> rpt $ goal_assum $ drule_at Any
  )
  >> drule_then irule wf_trace_cid_backward
  >> goal_assum $ rev_drule_at Any
  >> fs[]
QED

(* set of promises contains only elements smaller then the memory *)

Theorem wf_trace_EVERY_LENGTH_bst_prom_inv:
  !i tr cid p st.
  wf_trace tr /\ i < LENGTH tr
  /\ Core cid p st IN FST $ EL i tr
  ==> EVERY (λx. x <= LENGTH $ SND $ EL i tr) st.bst_prom 
Proof
  Induct
  >- (
    rw[wf_trace_def,empty_prom_def]
    >> res_tac >> fs[NULL_EQ]
  )
  >> rpt strip_tac
  >> drule_all_then assume_tac wf_trace_parstep_EL
  >> drule_all_then strip_assume_tac wf_trace_cid_backward1
  >> first_x_assum $ drule_then $ drule_at Any
  >> gvs[parstep_nice_def,parstep_cases,cstep_cases]
  >> drule_then (dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> gvs[]
  >- (imp_res_tac clstep_bst_prom_EQ >> fs[])
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

(* certified traces have empty promises in the last state *)

Theorem wf_trace_LAST_NULL_bst_prom:
  !tr cid p st. wf_trace tr
  /\ Core cid p st IN FST $ LAST tr
  ==> NULL st.bst_prom
Proof
  rpt strip_tac
  >> imp_res_tac wf_trace_NOT_NULL
  >> Cases_on `LENGTH tr = 1`
  >- (
    gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL,wf_trace_def,empty_prom_def]
    >> res_tac
  )
  >> spose_not_then assume_tac
  >> gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL,NOT_NUM_EQ]
  >> `parstep_nice (EL (PRE $ PRE $ LENGTH tr) tr) (EL (PRE $ LENGTH tr) tr)` by (
    gs[LESS_OR_EQ]
    >- (
      `0 < PRE $ LENGTH tr` by DECIDE_TAC
      >> drule_then (qspec_then `PRE $ PRE $ LENGTH tr` mp_tac) wf_trace_parstep_EL
      >> fs[SUC_PRE]
    )
    >> REWRITE_TAC[Excl"EL",Excl"EL_restricted",GSYM EL,ONE]
    >> drule_then irule wf_trace_parstep_EL
    >> fs[]
  )
  >> gvs[parstep_nice_def,parstep_cases]
  >- (
    (* TODO pick the previous index with progress in the state *)
    cheat
  )
  >> fs[is_certified_def]
  >> drule_then assume_tac cstep_seq_rtc_bst_prom_EQ
  >> qmatch_assum_abbrev_tac `A ==> _ /\ _`
  >> `A` by (
    >> fs[Abbr`A`]
    >> drule_then irule wf_trace_EVERY_LENGTH_bst_prom_inv
    >> dsimp[]
  )
  >> gvs[]
QED

val _ = export_theory();
