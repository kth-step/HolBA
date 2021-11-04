open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "spinlock";

val (bir_spinlock_progbin_def, bir_spinlock_prog_def, bir_is_lifted_prog_spinlock) = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

open bir_promisingTheory rich_listTheory listTheory arithmeticTheory;

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
  is_promise cid t M M' system1 system2 =
  ?st st' p p' v l.
    Core cid p st IN system1
    /\ Core cid p' st' IN system2
    /\ t = LENGTH M + 1
    /\ M' = M ++ [<| loc := l; val := v; cid := cid  |>]
    /\ st'.bst_prom = st.bst_prom ++ [t]
End

(*
 * Defintion of traces
 *)

Definition parstep_nice_def:
  parstep_nice s1 s2 = parstep (FST s1) (SND s1) (FST s2) (SND s2)
End

(* set of all traces using bir_multicore$gen_traces *)
Definition par_traces_def:
  par_traces = gen_traces parstep_nice
End

Theorem par_traces_ind:
  !P. (!s. P [s])
  /\ (!s2 s1 t. P (t ++ [s1]) /\ parstep_nice s1 s2 ==> P (t ++ [s1; s2]))
  ==> !tr. tr IN par_traces ==> P tr
Proof
  fs[par_traces_def,bir_multicoreTheory.gen_traces_def]
  >> ntac 2 strip_tac
  >> `!ps tr. is_gen_trace ps tr ==> ps = parstep_nice ==> P tr` by (
    ho_match_mp_tac bir_multicoreTheory.is_gen_trace_ind
    >> fs[]
  )
  >> fs[]
QED

Theorem is_gen_trace_NOT_NULL:
  !R s. is_gen_trace R s ==> ~NULL s
Proof
  ho_match_mp_tac bir_multicoreTheory.is_gen_trace_ind
  >> fs[NULL_EQ]
QED

Theorem is_gen_trace_EL:
  !R s. is_gen_trace R s ==> !i. SUC i < LENGTH s ==> R (EL i s) (EL (SUC i) s)
Proof
  ho_match_mp_tac bir_multicoreTheory.is_gen_trace_ind
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
  !s1 s2. wf_sys $ FST s1
  /\ parstep_nice s1 s2
  ==> wf_sys $ FST s2
Proof
  `!s1 m1 s2 m2. parstep s1 m1 s2 m2 ==> wf_sys s1 ==> wf_sys s2` by (
    ho_match_mp_tac bir_promisingTheory.parstep_ind
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
  rw[wf_trace_def,par_traces_def,bir_multicoreTheory.gen_traces_def]
  >> imp_res_tac is_gen_trace_NOT_NULL
QED

Theorem wf_trace_parstep_EL:
  !tr i. wf_trace tr /\ SUC i < LENGTH tr ==> parstep_nice (EL i tr) (EL (SUC i) tr)
Proof
 fs[is_gen_trace_EL,wf_trace_def,par_traces_def,bir_multicoreTheory.gen_traces_def]
QED

Theorem par_traces_wf_sys_monotone:
  !tr i.
    tr IN par_traces /\ wf_sys $ FST $ HD tr
    /\ i < LENGTH tr ==> wf_sys $ FST $ EL i tr
Proof
  `!ps tr. is_gen_trace ps tr ==>
    ps = parstep_nice /\ wf_sys (FST (HD tr)) ==>
     !i. i < LENGTH tr ==> wf_sys (FST (EL i tr))` by (
    ho_match_mp_tac bir_multicoreTheory.is_gen_trace_ind
    >> rw[]
    >- (qmatch_assum_rename_tac `i < 1` >> Cases_on `i` >> fs[])
    >> qmatch_assum_rename_tac `i < LENGTH t + 2`
    >> Cases_on `NULL t`
    >- (
      fs[NULL_EQ,EL_APPEND1,EL_APPEND2]
      >> fs o single $
        (REWRITE_CONV [GSYM COUNT_LIST_COUNT,
        GSYM pred_setTheory.IN_COUNT]
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
  >> fs[par_traces_def,bir_multicoreTheory.gen_traces_def]
QED

Theorem wf_trace_wf_sys:
  !tr cid p st p' st' i. wf_trace tr
  /\ Core cid p st IN FST (EL i tr)
  /\ Core cid p' st' IN FST (EL i tr)
  /\ i < LENGTH tr
  ==> p = p' /\ st = st'
Proof
  rpt gen_tac >> strip_tac
  >> fs[wf_trace_def]
  >> drule_all par_traces_wf_sys_monotone
  >> simp[wf_sys_def]
  >> disch_then $ dxrule_all
  >> fs[]
QED

Theorem wf_trace_is_promise_MEM_trace:
  !tr cid t i M s. wf_trace tr
  /\ is_promise cid t (SND $ EL i tr) M (FST $ EL i tr) s
  /\ i < LENGTH tr
  ==>  SUC i < LENGTH tr /\ M = SND $ EL (SUC i) tr /\ s = FST $ EL (SUC i) tr
Proof
  cheat
QED

Theorem wf_trace_is_fulfil_MEM_trace:
  !tr cid t i s. wf_trace tr
  /\ is_fulfil cid t (FST $ EL i tr) s
  /\ i < LENGTH tr
  ==>  SUC i < LENGTH tr /\ s = FST $ EL (SUC i) tr
Proof
  cheat
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
  /\ is_promise cid t (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ is_promise cid' t' (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  ==> cid = cid' /\ t = t'
Proof
  cheat
QED

(* same core id occurs in next step in the trace *)
Theorem wf_trace_cid_forward1:
  !tr i cid p st. wf_trace tr /\ Core cid p st IN FST (EL i tr)
  /\ SUC i < LENGTH tr
  ==> ?p st. Core cid p st IN FST (EL (SUC i) tr)
Proof
  cheat
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
  cheat
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

(* memory is monotonic only ever increases, at most by one *)

Theorem parstep_nice_memory_imp:
  !s1 s2. parstep_nice s1 s2
  ==> SND s1 = SND s2 \/ ?m. SND s2 = SND s1 ++ [m]
Proof
  fs[par_traces_def,bir_multicoreTheory.gen_traces_def,parstep_nice_def,pairTheory.FORALL_PROD]
  >> rw[bir_promisingTheory.cstep_cases,bir_promisingTheory.parstep_cases]
  >> disj2_tac
  >> irule_at Any EQ_REFL
QED

(* certified traces have empty promises in the last state *)

Theorem wf_trace_LAST_NULL_bst_prom:
  !tr cid p st. wf_trace tr
  /\ Core cid p st IN FST $ LAST tr
  ==> NULL st.bst_prom
Proof
  cheat
QED

(* a promise entails lower bound of future memory length *)

Theorem is_promise_LENGTH_SND_EL:
  !i j tr cid t. wf_trace tr
  /\ is_promise cid t (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
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
  >> drule_all_then assume_tac wf_trace_parstep_EL
  >> dxrule_then strip_assume_tac parstep_nice_memory_imp
  >> gs[]
  >> `SUC i + SUC v = SUC $ v + SUC i` by fs[]
  >> pop_assum $ fs o single
QED

(* a promise is only promised once *)

Theorem is_promise_once:
  !i j tr cid cid' t. wf_trace tr
  /\ is_promise cid t (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ i < j /\ SUC j < LENGTH tr
  ==> ~is_promise cid' t (SND $ EL j tr) (SND $ EL (SUC j) tr)
    (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> rev_drule_at Any is_promise_LENGTH_SND_EL
  >> disch_then $ rev_drule_at_then Any assume_tac
  >> first_assum $ qspec_then `j` assume_tac
  >> first_x_assum $ qspec_then `SUC j` assume_tac
  >> dxrule_then strip_assume_tac $ iffLR is_promise_def
  >> gvs[]
QED

Theorem clstep_bst_prom_EQ:
  clstep p cid st M [] st' ==> st.bst_prom = st'.bst_prom
Proof
  rw[bir_promisingTheory.clstep_cases]
  >> gvs[bir_programTheory.bir_state_t_accfupds,bir_programTheory.bir_exec_stmt_def,bir_programTheory.bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_programTheory.bir_state_set_typeerror_def,stmt_generic_step_def]
  >> cheat
QED

(* a fulfil has an earlier promise *)

Theorem NOT_is_promise_NOT_MEM_bst_prom:
  !i tr cid p st p' st' t. wf_trace tr
  /\ ~is_promise cid t (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
  /\ SUC i < LENGTH tr
  /\ Core cid p st IN FST $ EL i tr
  /\ ~MEM t st.bst_prom
  /\ Core cid p' st' IN FST $ EL (SUC i) tr
  ==> ~MEM t st'.bst_prom
Proof
  rw[]
  >> drule_all_then strip_assume_tac wf_trace_parstep_EL
  >> fs[parstep_nice_def,bir_promisingTheory.parstep_cases]
  >> Cases_on `cid = cid'`
  >- (
    pop_assum $ fs o single
    >> drule_then (dxrule_then drule) wf_trace_wf_sys
    >> rw[]
    >> fs[is_promise_def,DISJ_EQ_IMP]
    >> first_x_assum drule
    >> fs[AND_IMP_INTRO,AC CONJ_ASSOC CONJ_COMM,bir_promisingTheory.cstep_cases]
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
  ==> ?j. j < i
    /\ is_promise cid t (SND $ EL j tr) (SND $ EL (SUC j) tr)
      (FST $ EL j tr) (FST $ EL (SUC j) tr)
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
  >> fs[parstep_nice_def,bir_promisingTheory.parstep_cases,is_fulfil_def,DISJ_EQ_IMP]
  >> Cases_on `cid = cid'`
  >- (
    pop_assum $ fs o single
    >> drule_then (dxrule_then drule) wf_trace_wf_sys
    >> rw[]
    >> fs[bir_promisingTheory.cstep_cases]
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
  /\ is_promise cid t (SND $ EL i tr) (SND $ EL (SUC i) tr)
    (FST $ EL i tr) (FST $ EL (SUC i) tr)
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
    >> `?p st. Core cid p st IN FST $ EL (SUC $ i + v) tr` by (
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
  cheat
QED

(*
 * exclusive store and read pairs
 *)

(* TODO correct return value of bir_get_current_statement *)
Definition is_read_xcl_def:
  is_read_xcl cid t sys1 sys2 <=>
  ?st st' p p' var mem_e a_e en ty.
    Core cid p st IN sys1
    /\ Core cid p' st' IN sys2
    (* /\ st'.bst_pc = bir_pc_next *)
    /\ bir_get_current_statement p st.bst_pc
     = SOME $ BStmtB $ BStmt_Assign var $ BExp_Load mem_e a_e en ty
End

(* TODO correct return value of bir_get_current_statement *)
Definition is_fulfil_xcl_def:
  is_fulfil_xcl cid t sys1 sys2 <=>
    is_fulfil cid t sys1 sys2
  /\ ?st st' p p' var mem_e a_e en v_e.
    Core cid p st IN sys1
    /\ Core cid p' st' IN sys2
    (* /\ st'.bst_pc = bir_pc_next *)
    /\ bir_get_current_statement p st.bst_pc
      = SOME $ BStmtB $ BStmt_Assign var $ BExp_Store mem_e a_e en v_e
End

(* only exclusive loads set the exclusive bank *)

Theorem xclb_NONE_SOME_is_read_xclb:
  !t v cid p p' st st' i tr. wf_trace tr /\ SUC i < LENGTH tr
  /\ Core cid p st IN FST $ EL i tr
  /\ Core cid p' st' IN FST $ EL (SUC i) tr
  (* TODO /\ st'.xclb = SOME <| time := t ; view = v |>
          /\ st.xclb = NONE *)
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
    ==> ARB
      (* TODO the exclusive bank is unmodified *)
      (* st.xclb = st'.xclb  *)
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
    ; bst_fwdb := (\l. <| time:= 0; view:=0; xcl:=F |>)
    ; bst_counter := 0
    (* TODO st.bst_xclb = NONE *)
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

(* spinlock cores fulfil to the mutex address *)
(* TODO add mutex address *)
Theorem is_fulfil_to:
  !tr cid. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  ==> ARB
Proof
  cheat
QED


(* Theorem 4 : any exclusive fulfil reads from timestamp 0 onwards *)

Theorem cores_run_spinlock_is_fulfil_xcl_initial_xclb:
  !tr cid t i s p st. wf_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ is_fulfil_xcl cid t (FST $ EL i tr) s
  /\ Core cid p st IN (FST $ EL i tr)
  ==> ?x. (* TODO st.bst_xclb = SOME x /\ *) x.time = 0
Proof
  cheat
QED

(* any exiting core must have fulfiled exclusively *)

Theorem core_runs_spinlock_IS_NONE_bst_pc_is_fulfil_xcl:
  !tr cid p st. wf_trace tr
  /\ core_runs_spinlock cid (FST $ HD tr)
  /\ Core cid p st IN (FST $ LAST tr)
  /\ IS_NONE $ bir_get_current_statement p st.bst_pc
  ==> ?i t. SUC i < LENGTH tr
    /\ is_fulfil_xcl cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
Proof
  cheat
QED

(* distinct exclusive fulfils enforce an ordering on their timestamps *)

Theorem core_runs_spinlock_is_fulfil_xcl_timestamp_order:
  !tr cid cid' t t' i j i' j' t t'. wf_trace tr
  /\ core_runs_spinlock cid (FST (HD tr))
  /\ core_runs_spinlock cid' (FST (HD tr))
  /\ is_fulfil_xcl cid t (FST (EL i tr)) (FST (EL (SUC i) tr))
  /\ is_fulfil_xcl cid' t' (FST (EL i' tr)) (FST (EL (SUC i') tr))
  /\ is_promise cid t (SND (EL j tr)) (SND (EL (SUC j) tr))
    (FST (EL j tr)) (FST (EL (SUC j) tr))
  /\ is_promise cid' t' (SND (EL j' tr)) (SND (EL (SUC j') tr))
    (FST (EL j' tr)) (FST (EL (SUC j') tr))
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
(* TODO add assumption on mutex address for other cores *)
Theorem core_runs_spinlock_correct:
  !tr cid cid' t i s p p' st st'. wf_trace tr
  /\ core_runs_spinlock cid $ FST $ HD tr
  /\ core_runs_spinlock cid' $ FST $ HD tr
  /\ Core cid p st IN (FST $ LAST tr)
  /\ Core cid' p' st' IN (FST $ LAST tr)
  /\ IS_NONE $ bir_get_current_statement p st.bst_pc
  /\ IS_NONE $ bir_get_current_statement p' st'.bst_pc
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

(*
fetch "-" "bir_spinlock_prog_def"
bir_spinlock_progbin_def
*)

val _ = export_theory();
