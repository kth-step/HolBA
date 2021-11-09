open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "spinlock";

val (bir_spinlock_progbin_def, bir_spinlock_prog_def, bir_is_lifted_prog_spinlock) = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory tracesTheory;

(*
 * characterisation of fulfil and promise rules
 *)

Definition is_fulfil_def:
  is_fulfil cid t system1 system2 =
  ?st st' p p'.
    Core cid p st IN system1
    /\ Core cid p' st' IN system2
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
End

Theorem is_fulfil_MEM_bst_prom:
  is_fulfil cid t system1 system2
  ==> ?p st. Core cid p st IN system1  /\ MEM t st.bst_prom
Proof
  fs[is_fulfil_def] >> metis_tac[]
QED

Definition is_promise_def:
  is_promise cid t sys1 sys2 =
  ?st st' p p' v l.
    Core cid p st IN FST sys1
    /\ Core cid p' st' IN FST sys2
    /\ t = LENGTH (SND sys1) + 1
    /\ (SND sys2) = (SND sys1) ++ [<| loc := l; val := v; cid := cid  |>]
    /\ st'.bst_prom = st.bst_prom ++ [t]
End

(* fulfil steps change the state *)

Theorem is_fulfil_state_changed:
  !tr cid t p p' st st' i. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ Core cid p st IN (FST $ EL i tr)
  /\ Core cid p' st' IN (FST $ EL (SUC i) tr)
  ==> st <> st'
Proof
  rpt strip_tac >> gvs[is_fulfil_def,wf_sys_def]
  >> qpat_x_assum `MEM _ _` mp_tac
  >> drule_then (dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> drule_then (rev_dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> gvs[]
  >> qpat_x_assum `FILTER _ _ = _` $ ONCE_REWRITE_TAC o single o GSYM
  >> fs[MEM_FILTER]
QED

(* promising steps change the state *)

Theorem is_promise_state_changed:
  !tr cid t p p' st st' i. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ Core cid p st IN (FST $ EL i tr)
  /\ Core cid p' st' IN (FST $ EL (SUC i) tr)
  ==> st <> st'
Proof
  rpt strip_tac >> gvs[is_promise_def,wf_sys_def]
  >> drule_then (dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> drule_then (rev_dxrule_then $ drule_then assume_tac) wf_trace_wf_sys
  >> gvs[]
QED

(* parstep and fulfil transitions have same ids *)

Theorem is_fulfil_parstep_nice:
  !tr i cid cid'. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid = cid'
Proof
  cheat
QED

(* parstep and promise transitions have same ids *)

Theorem is_promise_parstep_nice:
  !tr i cid cid'. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ parstep_nice cid' (EL i tr) (EL (SUC i) tr)
  ==> cid = cid'
Proof
  cheat
QED

(* fulfil steps affect only the promising core *)

Theorem is_fulfil_inv:
  !tr cid cid' t p p' p2 p2' st st' st2 st2' i.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ Core cid p st IN (FST $ EL i tr)
  /\ Core cid p' st' IN (FST $ EL (SUC i) tr)
  /\ Core cid' p2 st2 IN FST (EL i tr)
  /\ Core cid' p2' st2' IN FST (EL (SUC i) tr)
  /\ cid <> cid'
  ==> st <> st' /\ p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    drule_then irule is_fulfil_state_changed
    >> rpt $ goal_assum $ drule_at Any
  )
  >>  drule_then (drule_then irule) wf_trace_unchanged
  >> rpt $ goal_assum $ drule_at Any
QED

(* promise steps affect only the promising core *)

Theorem is_promise_inv:
  !tr cid cid' t p p' p2 p2' st st' st2 st2' i.
  wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ Core cid p st IN (FST $ EL i tr)
  /\ Core cid p' st' IN (FST $ EL (SUC i) tr)
  /\ Core cid' p2 st2 IN FST (EL i tr)
  /\ Core cid' p2' st2' IN FST (EL (SUC i) tr)
  /\ cid <> cid'
  ==> st <> st' /\ p2 = p2' /\ st2 = st2'
Proof
  rpt gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    drule_then irule is_promise_state_changed
    >> rpt $ goal_assum $ drule_at Any
  )
  >>  drule_then (drule_then irule) wf_trace_unchanged
  >> rpt $ goal_assum $ drule_at Any
QED

(* a promise entails lower bound of future memory length *)

Theorem is_promise_LENGTH_SND_EL:
  !i j tr cid t. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ SUC i <= j /\ j < LENGTH tr
  ==> t <= LENGTH (SND $ EL j tr)
Proof
  rpt gen_tac
  >> Induct_on `j - SUC i`
  >- (rw[is_promise_def] >> gs[LESS_OR_EQ])
  >> rw[SUB_LEFT_EQ]
  >> first_x_assum $ rev_drule_at Any
  >> disch_then $ rev_drule_at Any
  >> disch_then $ qspec_then `v + SUC i` assume_tac
  >> `SUC $ v + SUC i < LENGTH tr` by fs[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> dxrule_then strip_assume_tac parstep_nice_memory_imp
  >> gs[]
  >> `SUC i + SUC v = SUC $ v + SUC i` by fs[]
  >> pop_assum $ fs o single
QED

(* a promise is only promised once *)

Theorem is_promise_once:
  !i j tr cid cid' t. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ i < j /\ SUC j < LENGTH tr
  ==> ~is_promise cid' t (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> rev_drule_at Any is_promise_LENGTH_SND_EL
  >> disch_then $ rev_drule_at_then Any assume_tac
  >> first_assum $ qspec_then `j` assume_tac
  >> first_x_assum $ qspec_then `SUC j` assume_tac
  >> dxrule_then strip_assume_tac $ iffLR is_promise_def
  >> gvs[]
QED

(* a fulfil has an earlier promise *)

Theorem NOT_is_promise_NOT_MEM_bst_prom:
  !i tr cid p st p' st' t. wf_trace tr
  /\ ~is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  /\ Core cid p st IN FST $ EL i tr
  /\ ~MEM t st.bst_prom
  /\ Core cid p' st' IN FST $ EL (SUC i) tr
  ==> ~MEM t st'.bst_prom
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,parstep_cases]
  >> Cases_on `cid = cid'`
  >- (
    pop_assum $ fs o single
    >> drule_then (dxrule_then drule) wf_trace_wf_sys
    >> rw[]
    >> fs[is_promise_def,DISJ_EQ_IMP]
    >> first_x_assum drule
    >> fs[AND_IMP_INTRO,AC CONJ_ASSOC CONJ_COMM,cstep_cases]
    >- (dxrule_then assume_tac clstep_bst_prom_EQ >> fs[])
    >> rpt strip_tac
    >> Cases_on `msg`
    >> gvs[AND_IMP_INTRO,mem_msg_t_val,mem_msg_t_loc,mem_msg_t_cid]
    >> cheat
  )
  >> `Core cid p st IN FST $ EL (SUC i) tr` by fs[EQ_SYM_EQ]
  >> dxrule wf_trace_wf_sys
  >> ntac 2 $ disch_then dxrule >> strip_tac >> gs[]
QED

Theorem is_fulfil_is_promise:
  !i tr cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> ?j. j < i /\ is_promise cid t (EL j tr) (EL (SUC j) tr)
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[DISJ_EQ_IMP]
  >> `!j p st. j <= i /\ Core cid p st IN FST $ EL j tr ==> ~MEM t st.bst_prom` by (
    Induct
    >- (
      rw[] >> fs[wf_trace_def,empty_prom_def]
      >> strip_tac
      >> res_tac
      >> gs[NULL_EQ]
    )
    >> rw[] >> gs[]
    >> `j < i` by fs[]
    >> first_x_assum $ dxrule_then assume_tac
    >> drule_then drule wf_trace_cid_backward1
    >> rw[]
    >> first_x_assum $ drule_then assume_tac
    >> drule_then drule NOT_is_promise_NOT_MEM_bst_prom
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >> fs[is_fulfil_def]
  >> first_x_assum $ rev_drule_at Any
  >> fs[]
QED

(* a promise has a succeeding fulfil *)

Theorem NOT_is_fulfil_MEM_bst_prom:
  !i tr cid p st p' st' t. wf_trace tr /\ SUC i < LENGTH tr
  /\ ~is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ Core cid p st IN FST $ EL i tr
  /\ MEM t st.bst_prom
  /\ Core cid p' st' IN FST $ EL (SUC i) tr
  ==> MEM t st'.bst_prom
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,parstep_cases,is_fulfil_def,DISJ_EQ_IMP]
  >> Cases_on `cid = cid'`
  >- (
    pop_assum $ fs o single
    >> drule_then (dxrule_then drule) wf_trace_wf_sys
    >> rw[]
    >> fs[cstep_cases]
    >> drule_then assume_tac clstep_bst_prom_EQ
    >> fs[]
  )
  >> first_x_assum $ rev_drule_then drule
  >> `Core cid p st IN FST $ EL (SUC i) tr` by fs[EQ_SYM_EQ]
  >> dxrule wf_trace_wf_sys
  >> ntac 2 $ disch_then dxrule >> strip_tac >> gs[]
QED

Theorem is_promise_is_fulfil:
  !i j tr cid t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  ==> ?j. i < j
    /\ is_fulfil cid t (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[DISJ_EQ_IMP]
  >> `!j p st. i <= j /\ SUC j < LENGTH tr
    /\ Core cid p st IN FST $ EL (SUC j) tr ==> MEM t st.bst_prom` by (
    Induct_on `j - i`
    >- (
      rw[] >> gvs[LESS_OR_EQ,is_promise_def]
      >> drule_then (dxrule_then drule) wf_trace_wf_sys
      >> rw[]
    )
    >> rw[SUB_LEFT_EQ] >> fs[]
    >> first_x_assum $ qspecl_then [`i + v`,`i`] mp_tac
    >> fs[]
    >> `?st. Core cid p st IN FST $ EL (SUC $ i + v) tr` by (
      irule wf_trace_cid_backward1
      >> `SUC $ i + SUC v = SUC $ SUC $ i + v` by fs[]
      >> pop_assum $ fs o single
      >> goal_assum drule
    )
    >> disch_then $ drule_then assume_tac
    >> drule NOT_is_fulfil_MEM_bst_prom
    >> rpt $ disch_then $ drule_at Any
    >> disch_then irule
    >> fs[]
    >> `SUC $ i + SUC v = SUC $ SUC $ i + v` by fs[]
    >> pop_assum $ fs o single
    >> goal_assum drule
  )
  >> `?p st. Core cid p st IN FST $ LAST tr` by (
    fs[is_promise_def,GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL]
    >> qexists_tac `p`
    >> drule_then irule wf_trace_cid_forward
    >> fs[]
    >> goal_assum $ drule_at Any
    >> fs[]
  )
  >> drule_all wf_trace_LAST_NULL_bst_prom
  >> gs[GSYM LENGTH_NOT_NULL,GSYM NULL_EQ,LAST_EL]
  >> Cases_on `SUC i = PRE $ LENGTH tr`
  >- (
    fs[is_promise_def]
    >> drule_then (dxrule_then drule) wf_trace_wf_sys
    >> rw[]
  )
  >> gs[NOT_NUM_EQ]
  >> `i <= PRE $ PRE $ LENGTH tr` by fs[]
  >> first_x_assum dxrule
  >> `0 < PRE $ LENGTH tr` by fs[]
  >> fs[iffLR SUC_PRE]
  >> disch_then drule
  >> rw[LENGTH_NOT_NULL,MEM_SPLIT,NOT_NULL_MEM]
  >> goal_assum drule
QED

(* a fulfil is only fulfilled once *)

Theorem is_fulfil_once:
  !tr i j t cid cid'. wf_trace tr
  /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC j < LENGTH tr /\ i <> j
  ==> ~is_fulfil cid' t (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  `!tr i j t cid cid'. wf_trace tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC j < LENGTH tr /\ i < j
  ==> ~is_fulfil cid' t (FST $ EL j tr) (FST $ EL (SUC j) tr) ` by (
    cheat
  )
  >> cheat
  (* TODO prove
  wlog_tac ``i < j`` [``i``,``j``]
  >> fs[NOT_NUM_EQ] THEN_LT USE_SG_THEN ASSUME_TAC 1 2
  DB.match["arithmetic"]``_:num <> _ <=> _`` *)
QED

(* only one fulfil happens at a time *)


Theorem is_fulfil_same:
  !tr cid cid' t t' i. wf_trace tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil cid' t' (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> cid = cid' /\ t = t'
Proof
  cheat
QED

(* only one promise happens at a time *)

Theorem is_promise_same:
  !tr cid cid' t t' i. wf_trace tr
  /\ is_promise cid t (EL i tr) (EL (SUC i) tr)
  /\ is_promise cid' t' (EL i tr) (EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> cid = cid' /\ t = t'
Proof
  cheat
QED

(*
 * exclusive store and read pairs
 *)

Definition is_read_xcl_def:
  is_read_xcl cid t sys1 sys2 <=>
  ?st st' p.
    Core cid p st IN sys1
    /\ Core cid p st' IN sys2
    /\ st.bst_pc = bir_pc_next st'.bst_pc
    /\ is_xcl_read p st
End

Definition is_fulfil_xcl_def:
  is_fulfil_xcl cid t sys1 sys2 <=>
    is_fulfil cid t sys1 sys2
  /\ ?st st' p.
    Core cid p st IN sys1
    /\ Core cid p st' IN sys2
    /\ st.bst_pc = bir_pc_next st'.bst_pc
    /\ is_xcl_write p st
End

(* only exclusive loads set the exclusive bank *)

Theorem xclb_NONE_SOME_is_read_xclb:
  !t v cid p p' st st' i tr. wf_trace tr /\ SUC i < LENGTH tr
  /\ Core cid p st IN FST $ EL i tr
  /\ Core cid p' st' IN FST $ EL (SUC i) tr
  /\ st'.bst_xclb = SOME <| xclb_time := t; xclb_view := v |>
  /\ st.bst_xclb = NONE
  ==> ?t. is_read_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
Proof
  cheat
QED

(* an exclusive store has an earlier exclusive load *)

Theorem is_fulfil_xcl_is_read_xcl:
  !i tr cid p st t. wf_trace tr /\ SUC i < LENGTH tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ Core cid p st IN FST $ EL (SUC i) tr
  ==> ?j. j < i
    /\ is_read_xcl cid t (FST $ EL j tr) (FST $ EL (SUC j) tr)
    /\ !k p' st'. j < k /\ k <= i /\ Core cid p' st' IN FST $ EL k tr
    ==> st.bst_xclb = st'.bst_xclb
Proof
  rpt strip_tac
  (* TODO there is a (last) process that sets the exclusive bank *)
  (* TODO by xclb_NONE_SOME_is_read_xclb, this is an exclusive load *)
  >> cheat
QED

(*
 * correctness of spinlock
 *)

Definition core_runs_prog_def:
  core_runs_prog cid s prog =
    ?st. Core cid prog st IN s
    /\ st = <|
      bst_pc      := bir_program$bir_pc_first prog
    ; bst_environ  := bir_env_default $ bir_envty_of_vs $
                        bir_varset_of_program prog
    ; bst_status := BST_Running
    ; bst_viewenv := FEMPTY
    ; bst_coh := \x.0
    ; bst_v_rOld := 0
    ; bst_v_CAP := 0
    ; bst_v_rNew := 0
    ; bst_v_wNew := 0
    ; bst_v_wOld := 0
    ; bst_prom := []
    ; bst_inflight := []
    ; bst_fwdb := (\l. <| fwdb_time:= 0; fwdb_view:=0; fwdb_xcl:=F |>)
    ; bst_counter := 0
    ; bst_xclb := NONE
  |>
End

Definition core_runs_spinlock_def:
  core_runs_spinlock cid s =
    core_runs_prog cid s (bir_spinlock_prog:string bir_program_t)
End

Definition cores_run_spinlock_def:
  cores_run_spinlock s =
    !cid p st. Core cid p st IN s
      ==> core_runs_spinlock cid s
End

(* Theorem 4 : any exclusive fulfil reads from timestamp 0 onwards *)

Theorem cores_run_spinlock_is_fulfil_xcl_initial_xclb:
  !tr cid t i s p st. wf_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) s
  /\ Core cid p st IN (FST $ EL i tr)
  ==> IS_SOME st.bst_xclb /\ (THE st.bst_xclb).xclb_time = 0
Proof
  cheat
QED

(* any exiting core must have fulfiled exclusively *)

Theorem core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl:
  !tr cid p st. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ Core cid p st IN (FST $ LAST tr)
  /\ st.bst_status = BST_JumpOutside l
  ==> ?i t. SUC i < LENGTH tr
    /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
Proof
  cheat
QED

(* distinct exclusive fulfils enforce an ordering on their timestamps *)
(* TODO replace "is_fulfil_xcl" assumptions with t and t' have same address *)
Theorem core_runs_spinlock_is_fulfil_xcl_timestamp_order:
  !tr cid cid' t t' i j i' j' t t'. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ core_runs_spinlock cid' (FST $ HD tr)
  /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_fulfil_xcl cid' t' (FST $ EL i' tr) (FST $ EL (SUC i') tr)
  /\ is_promise cid t (EL j tr) (EL (SUC j) tr)
  /\ is_promise cid' t' (EL j' tr) (EL (SUC j') tr)
  /\ i <> i' /\ j < i /\ j' < i' /\ SUC i' < LENGTH tr
  ==> ~(t < t')
Proof
  rpt strip_tac
  >> drule_all_then assume_tac wf_trace_parstep_EL
  >> drule_then (rev_drule_then $ drule_then assume_tac)
    cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> drule_then (drule_then $ drule_then assume_tac)
    cores_run_spinlock_is_fulfil_xcl_initial_xclb
  >> gvs[parstep_nice_def,parstep_cases]
  (* contradiction with atomic predicate and exclusivity bank *)
  >> cheat
QED


(* Theorem 5 only one core can leave the lock region *)
Theorem core_runs_spinlock_correct:
  !tr cid cid' t i s p p' st st' l l'. wf_trace tr
  /\ cores_run_spinlock $ FST $ HD tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ core_runs_spinlock cid' $ FST $ HD tr
  /\ Core cid p st IN (FST $ LAST tr)
  /\ Core cid' p' st' IN (FST $ LAST tr)
  /\ st.bst_status = BST_JumpOutside l
  /\ st'.bst_status = BST_JumpOutside l'
  ==> cid = cid'
Proof
  rpt strip_tac
  >> drule_then assume_tac wf_trace_NOT_NULL
  >> drule_then drule core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl
  >> rpt $ disch_then $ dxrule
  >> drule_then rev_drule core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl
  >> rpt $ disch_then $ dxrule
  >> rw[]
  >> Cases_on `i = i'`
  >- (
    gvs[is_fulfil_xcl_def]
    >> dxrule is_fulfil_same
    >> rpt $ disch_then dxrule
    >> fs[]
  )
  >> Cases_on `t = t'`
  >- (
    Cases_on `i < i'`
    >> gvs[is_fulfil_xcl_def]
    >> dxrule is_fulfil_once
    >> disch_then $ dxrule_at_then (Pos $ el 2) assume_tac >> gs[LESS_EQ]
  )
  >> rev_drule_then assume_tac $ cj 1 $ iffLR is_fulfil_xcl_def
  >> drule_then assume_tac $ cj 1 $ iffLR is_fulfil_xcl_def
  >> ntac 2 $ drule_then (dxrule_at Any) is_fulfil_is_promise
  >> rw[]
  >> qmatch_assum_rename_tac `j' < i'`
  >> qmatch_assum_rename_tac `j < i`
  >> Cases_on `j' = j`
  >- (
    gvs[]
    >> dxrule is_promise_same
    >> rpt $ disch_then dxrule
    >> fs[]
  )
  >> `~(t < t')` by (
    drule_then rev_drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
    >> rpt $ disch_then drule
    >> fs[]
  )
  >> `~(t' < t)` by (
    drule_then drule core_runs_spinlock_is_fulfil_xcl_timestamp_order
    >> rpt $ disch_then rev_drule
    >> fs[]
  )
  >> fs[]
QED

val _ = export_theory();
