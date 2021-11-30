open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
open listRangeTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;

val _ = new_theory "bir_promising";

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val _ = Datatype‘
  mem_msg_t = <|
    loc : bir_val_t;
    val : bir_val_t;
    cid : num
    |>
’;

val _ = Datatype‘
  mem_t = <|
    bmst_lock        : num option;
    bmst_counter     : num;
    bmst_storebuffer : mem_msg_t list;
    |>
’;

val mem_default_value_def = Define ‘
  mem_default_value = BVal_Imm (Imm64 0w)
’;

val mem_read_aux_def = Define‘
   mem_read_aux l NONE = NONE
/\ mem_read_aux l (SOME msg) = if msg.loc = l then SOME msg.val else NONE
’;

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
  mem_read M l (t:num) = if t = 0
                         then SOME mem_default_value
                         else mem_read_aux l (oEL (t-1) M)
’;

val mem_timestamps_def = Define‘
  mem_timestamps l M = MAP SND (FILTER (\x. (case x of (msg,_) => msg.loc = l)) (ZIP (M,[1 .. (LENGTH M)])))
’;
  
val mem_read_view_def = Define‘
  mem_read_view a rk (f:fwdb_t) t = if f.fwdb_time = t then f.fwdb_view else t
’;

val bir_eval_view_aux_def = Define‘
  (bir_eval_view_aux NONE = (0:num))
  /\
  (bir_eval_view_aux (SOME view) = view)
’;


val bir_eval_view_of_exp = Define‘
  (bir_eval_view_of_exp (BExp_BinExp et e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_Cast cty e ity) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Den v) viewenv =
    bir_eval_view_aux (FLOOKUP viewenv v))
/\ (bir_eval_view_of_exp exp viewenv = 0)
’;

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
val bir_eval_exp_view_def = Define‘
  bir_eval_exp_view exp env viewenv =
  (bir_eval_exp exp env, bir_eval_view_of_exp exp viewenv)
’;

Theorem bir_eval_exp_view_sound:
  !exp env viewenv.
  ?y. (bir_eval_exp_view exp env viewenv) = (bir_eval_exp exp env, y)
Proof
 Induct >> (
  fs [bir_eval_exp_view_def] >>
  REPEAT STRIP_TAC
 ) >| [
  Cases_on ‘FLOOKUP viewenv b’ >| [
   EXISTS_TAC “0:num”,

   Q.EXISTS_TAC ‘x’],

  RULE_ASSUM_TAC SPEC_ALL >>
  fs [],

  RULE_ASSUM_TAC SPEC_ALL >>
  fs []
 ] >>
 EVAL_TAC
QED

val exp_is_load_def = Define `
  (exp_is_load (BExp_Load _ _ _ _) = T) /\
  (exp_is_load _ = F)
`;

val stmt_generic_step_def = Define`
   stmt_generic_step (BStmtB (BStmt_Assign _ _)) = F
/\ stmt_generic_step (BStmtB (BStmt_Fence _ _)) = F
/\ stmt_generic_step (BStmtE (BStmt_CJmp _ _ _)) = F
/\ stmt_generic_step _ = T
`;

val is_read_def = Define`
   is_read BM_Read = T
/\ is_read BM_Write = F
/\ is_read BM_ReadWrite = T
`;

val is_write_def = Define`
   is_write BM_Read = F
/\ is_write BM_Write = T
/\ is_write BM_ReadWrite = T
`;

(*
(* Checks if the memory expressions from lifted loads and stores
 * refers to regular memory or dummy memory. May look inside casts *)
(* TODO: Clarify *)
val contains_dummy_mem_def = Define`
  (contains_dummy_mem (BExp_Den (BVar mem_name mem_ty)) =
     if mem_name <> "MEM8" (* RISC-V regular memory *)
     then T
     else F) /\
  (contains_dummy_mem (BExp_Load mem_e a_e en ty) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Store mem_e a_e en v_e) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Cast cast_ty e imm_ty) =
     contains_dummy_mem e) /\
  (contains_dummy_mem _ = F)
`;
*)
        
(* Obtains an option type that contains the load arguments
 * needed to apply the read rule (can look inside one cast) *)
val get_read_args_def = Define`
  (get_read_args (BExp_Load mem_e a_e en ty) =
     SOME (a_e, NONE)) /\
  (get_read_args (BExp_Cast cast_ty load_e imm_ty) =
   case get_read_args load_e of
   | SOME (a_e, NONE) => SOME (a_e, SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_read_args _ = NONE)
`;

(* Obtains an option type that contains the store arguments
 * needed to apply the fulfil rule *)
val get_fulfil_args_def = Define`
  (get_fulfil_args (BExp_IfThenElse cond_e e1 e2) = get_fulfil_args e1) /\
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) =
   SOME (a_e, v_e)) /\
  (get_fulfil_args _ = NONE)
`;

val get_xclb_view_def = Define`
  (get_xclb_view xclb_opt =
   case xclb_opt of
   | SOME xclb => xclb.xclb_view
   | NONE => 0)
`;

val fulfil_atomic_ok_def = Define`
  (fulfil_atomic_ok M l cid s tw =
   case s.bst_xclb of
   | SOME xclb =>
     ((EL xclb.xclb_time M).loc = l) ==>
       (!t'. (xclb.xclb_time < t'
             /\ t' < tw
             /\ (EL t' M).loc = l) ==> (EL t' M).cid = cid)
   | NONE => F)
`;

val env_update_cast64_def = Define‘
  env_update_cast64 varname (BVal_Imm v) vartype env =
    bir_env_update varname (BVal_Imm (n2bs (b2n v) Bit64)) vartype env
’;

val fulfil_update_env_def = Define`
  fulfil_update_env p s xcl =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) =>
        bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 0w)) (bir_var_type var_succ) s.bst_environ
      | _ => NONE
    else SOME s.bst_environ
`;

val fulfil_update_viewenv_def = Define`
  fulfil_update_viewenv p s xcl v_post =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) => SOME (s.bst_viewenv |+ (var_succ, v_post))
      | _ => NONE
    else SOME s.bst_viewenv
`;

(* Upon the loading statement that is the first Assign in a lifted
 * Load-type instruction, checks if the block is trying to model
 * an exclusive-load *)
val is_xcl_read_def = Define‘
  is_xcl_read p s =
    case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
                       (BExp_Den (BVar varname (BType_Imm Bit64))) BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))))) => T
     | _ => F
’;

(* Upon the storing statement that is the first Assign in a lifted
 * Strore-type instruction, checks if the block is trying to model
 * an exclusive-store *)
val is_xcl_write_def = Define‘
  is_xcl_write p s =
    case bir_get_current_statement p (bir_pc_next (bir_pc_next s.bst_pc)) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))))) => T
     | _ => F
’;


(* TODO: "Generalising variable "ν_pre" in clause #0 (113:1-131:23)"? *)
(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v e a_e cast_opt xcl M l (t:num) v_pre v_post v_addr var (a:num) (rk:num) new_env cid. (*TODO fix type of a and rk *)
   (bir_get_current_statement p s.bst_pc =
   SOME (BStmtB (BStmt_Assign var e)))
 (* NOTE: The fact that get_read_args is not NONE means also
  *       that the expression e constitutes a load operation *)
 /\ get_read_args e = SOME (a_e, cast_opt)
 (* If next statement is the dummy exclusive-load statement,
  * we are dealing with an exclusive load *)
 /\ xcl = is_xcl_read p s
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 ∧ mem_read M l t = SOME v
 ∧ v_pre = MAX v_addr s.bst_v_rNew
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX ν_pre (s.bst_coh l))) ⇒ (EL t' M).loc ≠ l)
 ∧ v_post = MAX v_pre (mem_read_view a rk (s.bst_fwdb(l)) t)
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 ∧ s' = s with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
                  bst_environ := new_env;
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_xclb := if xcl
                              then SOME <| xclb_time := t; xclb_view := v_post |>
                              else s.bst_xclb;
                  bst_pc := if xcl
                            then (bir_pc_next o bir_pc_next) s.bst_pc
                            else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M [] s')
/\ (* fulfil *)
(!p s s' M v e a_e xcl l (t:num) v_pre v_post v_addr v_data var v_e cid new_env new_viewenv.
    ((bir_get_current_statement p s.bst_pc =
      SOME (BStmtB (BStmt_Assign var e)))
 /\ get_fulfil_args e = SOME (a_e, v_e)
  (* If next to next statement is the dummy exclusive-store statement,
   * we are dealing with an exclusive store *)
 /\ xcl = is_xcl_write p s
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
 /\ (xcl ==> fulfil_atomic_ok M l cid s t)
 /\ MEM t s.bst_prom
 /\ EL t M = <| loc := l; val := v; cid := cid  |>
 (* TODO: Use get_xclb_view or separate conjunct to extract option type? *)
 /\ v_pre = MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
                (if xcl
                 then get_xclb_view s.bst_xclb
                 else 0)
 /\ (MAX v_pre (s.bst_coh l) < t)
 /\ v_post = t
 /\ SOME new_env = fulfil_update_env p s xcl
 (* TODO: Update viewenv by v_post or something else? *)
 /\ SOME new_viewenv = fulfil_update_viewenv p s xcl v_post
 /\ s' = s with <| bst_viewenv := new_viewenv;
                   bst_prom updated_by (FILTER (\t'. t' <> t));
                   bst_environ := new_env;
                   bst_coh := (\lo. if lo = l
                                    then MAX (s.bst_coh l) v_post
                                    else s.bst_coh(lo));
                   bst_v_wOld := MAX s.bst_v_wOld v_post;
                   bst_v_CAP := MAX s.bst_v_CAP v_addr;
                   bst_fwdb := (\lo. if lo = l
                                     then <| fwdb_time := t;
                                             fwdb_view := MAX v_addr v_data;
                                             fwdb_xcl := xcl |>
                                     else s.bst_fwdb(lo));
                   bst_xclb := if xcl
                               then NONE
                               else s.bst_xclb;
                   bst_pc := if xcl
                             then (bir_pc_next o bir_pc_next) s.bst_pc
                             else bir_pc_next s.bst_pc |>)
 ==>
  clstep p cid s M [t] s')
/\ (* fence *)
(!p s s' K1 K2 M cid v.
   (((bir_get_current_statement p s.bst_pc =
     SOME (BStmtB (BStmt_Fence K1 K2))))
   /\ v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                     bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
                     bst_pc updated_by bir_pc_next |>)
==>
  clstep p cid s M [] s')
/\ (* branch (conditional jump) *)
(!p s s' M cid v oo s2 v_addr cond_e lbl1 lbl2 stm.
   (bir_get_current_statement p s.bst_pc = SOME stm
    /\ stm = BStmtE (BStmt_CJmp cond_e lbl1 lbl2)
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
    /\ bir_exec_stmt p stm s = (oo,s2)
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>)
==>
  clstep p cid s M [] s')

/\ (* Other BIR single steps *)
(!p s s' M cid stm oo.
   (bir_get_current_statement p s.bst_pc = SOME stm
    /\ stmt_generic_step stm
    /\ bir_exec_stmt p stm s = (oo,s'))
==>
  clstep p cid s M [] s')
`;

(* core steps *)
val (bir_cstep_rules, bir_cstep_ind, bir_cstep_cases) = Hol_reln`
(* execute *)
(!p cid s M s' prom.
  clstep p cid s M prom s'
==>
  cstep p cid s M prom s' M)

/\ (* promise *)
(!p cid s M s' t msg.
   (msg.cid = cid
   /\ t = LENGTH M + 1
   /\ s' = s with bst_prom updated_by (\pr. pr ++ [t]))
==>
  cstep p cid s M [t] s' (M ++ [msg]))
`;

(* core steps seq *)
val (bir_cstep_seq_rules, bir_cstep_seq_ind, bir_cstep_seq_cases) = Hol_reln`
(* seq *)
(!p cid s M s'.
  clstep p cid s M ([]:num list) s'
==>
  cstep_seq p cid (s, M) (s', M))

/\ (* write *)
(!p cid s M s' s'' M' t.
  (cstep p cid s M [t] s' M'
  /\ clstep p cid s' M' [t] s'')
==>
  cstep_seq p cid (s, M) (s'', M'))
`;

val cstep_seq_rtc_def = Define`cstep_seq_rtc p cid = (cstep_seq p cid)^*`

(* cstep_seq invariant *)

Theorem bir_exec_stmt_jmp_bst_prom:
  !st p lbl. st.bst_prom = (bir_exec_stmt_jmp p lbl st).bst_prom
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

Theorem clstep_bst_prom_EQ:
!p cid st M st'. 
  clstep p cid st M [] st' ==> st.bst_prom = st'.bst_prom
Proof
  rw[bir_clstep_cases]
  >> gvs[bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,stmt_generic_step_def,bir_exec_stmt_jmp_bst_prom]
  >> qmatch_assum_rename_tac `stmt_generic_step stm`
  >> Cases_on `stm`
  (* 4 subgoals *)
  >~ [`stmt_generic_step $ BStmtB _`]
  >-  (
    qmatch_assum_rename_tac `stmt_generic_step $ BStmtB b`
    >> Cases_on `b`
    >> fs[AllCaseEqs(),stmt_generic_step_def,bir_exec_stmt_def,pairTheory.ELIM_UNCURRY]
    >> BasicProvers.every_case_tac
    >> fs[bir_exec_stmtB_def,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_observe_def]
    >> BasicProvers.every_case_tac
    >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
  )
  >~ [`stmt_generic_step $ BStmtB _`]
  >-  (
    qmatch_assum_rename_tac `stmt_generic_step $ BStmtB b`
    >> Cases_on `b`
    >> fs[AllCaseEqs(),stmt_generic_step_def,bir_exec_stmt_def,pairTheory.ELIM_UNCURRY]
    >> BasicProvers.every_case_tac
    >> fs[bir_exec_stmtB_def,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_observe_def]
    >> BasicProvers.every_case_tac
    >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
  )
  >> qmatch_assum_rename_tac `stmt_generic_step $ BStmtE b`
  >> Cases_on `b`
  >> fs[stmt_generic_step_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_exec_stmt_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
QED

Theorem cstep_seq_bst_prom_EQ:
  !p cid sM sM'. cstep_seq p cid sM sM' /\ EVERY (λx. x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. x <= LENGTH $ SND sM') (FST sM').bst_prom /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac bir_cstep_seq_ind
  >> conj_tac >> rpt gen_tac >> strip_tac
  >- (imp_res_tac clstep_bst_prom_EQ >> fs[])
  >> strip_tac >> conj_asm1_tac
  >- (
    pop_assum mp_tac
    >> gvs[bir_cstep_cases,bir_clstep_cases,rich_listTheory.FILTER_APPEND,EVERY_FILTER]
    >> match_mp_tac EVERY_MONOTONIC
    >> fs[]
  )
  >> gvs[bir_clstep_cases,bir_cstep_cases,bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,bir_state_set_typeerror_def,stmt_generic_step_def,bir_exec_stmt_jmp_bst_prom,rich_listTheory.FILTER_APPEND]
  >> fs[Once EQ_SYM_EQ,FILTER_EQ_ID]
  >> qpat_x_assum `EVERY _ _.bst_prom` mp_tac
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem cstep_seq_rtc_bst_prom_EQ:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM' /\ EVERY (λx. x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. x <= LENGTH $ SND sM') (FST sM').bst_prom /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO,cstep_seq_rtc_def]
  >> ntac 2 gen_tac
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> drule_all cstep_seq_bst_prom_EQ
  >> fs[]
QED

val is_certified_def = Define`
is_certified p cid s M = ?s' M'.
  cstep_seq_rtc p cid (s, M) (s', M')
  /\ s'.bst_prom = []
`;

val _ = Datatype `core_t =
  Core num (string bir_program_t) bir_state_t
`;

val cores_pc_not_atomic_def = Define`
  cores_pc_not_atomic cores =
    ~?cid p s i bl.
     FLOOKUP cores cid = SOME (Core cid p s)
     /\ s.bst_pc.bpc_index <> 0
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, bl)
     /\ bl.bb_atomic = T
`;

val atomicity_ok_def = Define`
  atomicity_ok cid cores =
    cores_pc_not_atomic (cores \\ cid)
`;

(* system step *)
val (bir_parstep_rules, bir_parstep_ind, bir_parstep_cases) = Hol_reln`
(!p cid s s' M M' cores prom.
   (FLOOKUP cores cid = SOME (Core cid p s)
    /\ atomicity_ok cid cores
    /\ cstep p cid s M prom s' M'
    /\ is_certified p cid s' M')
==>
   parstep cid cores M (FUPDATE cores (cid, Core cid p s')) M')
`;

(* Core-local execution *)
val eval_clstep_read_def = Define‘
  eval_clstep_read s M var a_e xcl =
    let
      (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
      v_pre = MAX v_addr s.bst_v_rNew;
    in
      case l_opt of
	SOME l =>
	let
          t_max = MAX v_pre (s.bst_coh l);
	  ts    = FILTER (\t. EVERY (\t'. ((EL (t'-1) M).loc ≠ l)) [(t+1) .. t_max])
                         (0::mem_timestamps l M)
	in
	  LIST_BIND ts (\t.
		 let
                   v_opt  = mem_read M l t;
		   v_post = MAX v_pre (mem_read_view 0 0 (s.bst_fwdb(l)) t);
		 in
		   case v_opt of
		     SOME v =>
		       (case env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ) of
			 SOME new_env =>
			   [s with <| bst_environ := new_env;
                                      bst_viewenv updated_by (λenv. FUPDATE env (var, v_post));
				      bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_post);
				      bst_v_rOld  updated_by (MAX v_post);
				      bst_v_CAP   updated_by (MAX v_addr);
				      bst_xclb := if xcl
						  then SOME <| xclb_time := t; xclb_view := v_post |>
						  else s.bst_xclb;
				      bst_pc   := if xcl
                                                  then (bir_pc_next o bir_pc_next) s.bst_pc
                                                  else bir_pc_next s.bst_pc |>]
		        | _ => [])
		   | _ => [])
      | _ => []
’;

val eval_clstep_fulfil_def = Define‘
  eval_clstep_fulfil p cid s M a_e v_e xcl =
    let
      (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
      (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    in
      case (l_opt,v_opt) of
        (SOME l, SOME v) =>
          let
            v_pre = MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
                        (if xcl then get_xclb_view s.bst_xclb else 0);
            ts = FILTER (\t. (EL (t-1) M = <| loc := l; val := v; cid := cid  |>)
                             /\ (MAX v_pre (s.bst_coh l) < t)) (s.bst_prom);
          in
            LIST_BIND ts (\v_post.
              if (xcl ==> fulfil_atomic_ok M l cid s v_post)
              then
                case fulfil_update_env p s xcl of
                  SOME new_env =>
                    (case fulfil_update_viewenv p s xcl v_post of
                      SOME new_viewenv => 
			[s with <| bst_viewenv := new_viewenv;
                                   bst_environ := new_env;
                                   bst_prom   updated_by (FILTER (\t'. t' <> v_post));
				   bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
				   bst_v_wOld updated_by MAX v_post;
				   bst_v_CAP  updated_by MAX v_addr;
				   bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
							          fwdb_view := MAX v_addr v_data;
							          fwdb_xcl := F |>);
				   bst_xclb := if xcl then NONE else s.bst_xclb;
				   bst_pc := if xcl
					     then (bir_pc_next o bir_pc_next) s.bst_pc
					     else bir_pc_next s.bst_pc |>]
                      | _ => [])
                 | _ => []
              else [])
          | _ => []
’;

val eval_clstep_fence_def = Define‘
  eval_clstep_fence s K1 K2 =
  let v = MAX (if is_read K1 then s.bst_v_rOld else 0)
              (if is_write K1 then s.bst_v_wOld else 0)
  in
    [s with <| bst_v_rNew updated_by MAX (if is_read K2 then v else 0);
               bst_v_wNew updated_by MAX (if is_write K2 then v else 0);
               bst_pc     updated_by bir_pc_next |>]
’;

val eval_clstep_branch_def = Define‘
  eval_clstep_branch p s stm =
  case stm of
    BStmtE (BStmt_CJmp cond_e lbl1 lbl2) =>
      let (sv, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
      in
        case sv of
          SOME v =>
            let (oo,s2) = bir_exec_stmt p stm s
            in [s2 with <| bst_v_CAP updated_by MAX v_addr |>]
’;

val eval_clstep_exp_def = Define‘
  eval_clstep_exp s var ex =
  case bir_eval_exp_view ex s.bst_environ s.bst_viewenv
  of (SOME val, v_val) =>
       (case env_update_cast64 (bir_var_name var) val (bir_var_type var) (s.bst_environ) of
          SOME new_env =>
            [s with <| bst_environ := new_env;
                       bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                       bst_pc      updated_by bir_pc_next |>]
        | _ => [])
  | _ => []
’;

val eval_clstep_bir_step_def = Define‘
  eval_clstep_bir_step p s stm =
   let (oo,s') = bir_exec_stmt p stm s
   in [s']
’;

val eval_clstep_def = Define‘
  eval_clstep p cid s M =
    case bir_get_current_statement p s.bst_pc of
      SOME (BStmtB (BStmt_Assign var e)) =>
      (case get_read_args e of
         SOME (a_e, cast_opt) =>
         eval_clstep_read s M var a_e (is_xcl_read p s)
       | NONE =>
         (case get_fulfil_args e of
            SOME (a_e, v_e) =>
            eval_clstep_fulfil p cid s M a_e v_e (is_xcl_write p s)
          | NONE => eval_clstep_exp s var e))
    | SOME (BStmtB (BStmt_Fence K1 K2)) =>
      eval_clstep_fence s K1 K2
    | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
      eval_clstep_branch p s (BStmtE (BStmt_CJmp cond_e lbl1 lbl2))
    | SOME stm =>
      eval_clstep_bir_step p s stm
    | _ => []
’;


(*** Certify execution execution ***)
val eval_certify_def = Define‘
  (
  eval_certify p cid s M 0 =
  NULL s.bst_prom
  ) /\ (
  eval_certify p cid s M (SUC fuel) =
  (NULL s.bst_prom \/
   EXISTS (\s'. eval_certify p cid s' M fuel)
          (eval_clstep p cid s M))
  )
’;

(*** Non-promising-mode execution ***)
val eval_clstep_core = Define‘
  eval_clstep_core M (Core cid p s) =
  MAP (Core cid p) (eval_clstep p cid s M)
’;

val eval_clsteps_aux_def = Define‘
  (
  eval_clsteps_aux 0 M core = [core]
  ) /\ (
  eval_clsteps_aux (SUC f) M core = 
  LIST_BIND (eval_clstep_core M core)
            (eval_clsteps_aux f M)
  )
’;

(* Cartesian product for list *)
(* TODO: Move this to some place else *)
val CART_PROD_LIST_def = Define‘
  (
  CART_PROD_LIST [] = [[]]
  ) /\ (
  CART_PROD_LIST (l::ll) =
    LIST_BIND l (\h. MAP (\l'. h::l') (CART_PROD_LIST ll))
  )
’;

val eval_clsteps_def = Define‘
eval_clsteps f (cores, M) =
let
  cores_list = CART_PROD_LIST $ MAP (eval_clsteps_aux f M) cores
in
  MAP (\cores. (cores, M)) cores_list
’;

(*** Promsing-mode execution ***)
val eval_find_promises_def = Define‘
  (
  eval_find_promises p cid s M promises t 0 =
  if NULL s.bst_prom then promises else []
  ) ∧ (
  eval_find_promises p cid s M promises t (SUC f) =
  (case bir_get_current_statement p s.bst_pc of
     SOME (BStmtB (BStmt_Assign _ (BExp_Store _ a_e _ v_e))) =>
       (let
          (sl, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
          (sv, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
          msg = <| loc := THE sl; val := THE sv; cid := cid |>;
          v_pre = MAX v_addr $ MAX v_data $ MAX s.bst_v_CAP $ MAX s.bst_v_wNew
                      (if (is_xcl_write p s) then get_xclb_view s.bst_xclb else 0);
          coh = s.bst_coh (THE sl);
          M' = SNOC msg M;
          s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
          promises' = if (MAX v_pre coh) < t then msg::promises else promises;
        in
          LIST_BIND (eval_clstep p cid s' M')
                    (λs'. eval_find_promises p cid s' M' promises' t f))
   | _ => [])
  ++
  LIST_BIND (eval_clstep p cid s M)
            (λs'. eval_find_promises p cid s' M promises t f)
  )
’;

val eval_pstep_def = Define ‘
  eval_pstep p cid s M ff =
  let
    t = LENGTH M + 1;
    promises = nub $ eval_find_promises p cid s M [] t ff;
    s' = s with <| bst_prom updated_by (CONS t) |> 
  in
    MAP (λp. (s', SNOC p M)) promises
’;

val eval_pstep_core_def = Define ‘
  eval_pstep_core ff M (Core cid p s) =
  MAP (λsM. (Core cid p (FST sM), SND sM))
      (eval_pstep p cid s M ff)
’;

val update_core_def = Define ‘
  (
  update_core new_c [] = []
  ) ∧ (
  update_core (Core new_cid new_p new_st) (Core cid p st::cs) =
  if new_cid = cid then
    Core new_cid new_p new_st :: cs
  else
    Core cid p st :: update_core (Core new_cid new_p new_st) cs
  )
’;

val eval_psteps_def = Define ‘
  (
  eval_psteps ff 0 (cores, M) = [(cores, M)]
  ) ∧ (
  eval_psteps ff (SUC f) (cores, M) =
  case LIST_BIND cores (eval_pstep_core ff M) of
    [] => [(cores,M)]
  | cMs => LIST_BIND (MAP (\cM. (update_core (FST cM) cores, SND cM)) cMs)
                     (eval_psteps ff f)
  )
’;

(*** Combined Promising and Non-Promising executions. ***)
val eval_promising_def = Define‘
  eval_promising fuel (cores, M) =
  LIST_BIND (eval_psteps fuel (fuel * LENGTH cores) (cores, M))
            (eval_clsteps fuel)
’;

(* Example *)

val core1_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
     (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
      (BExp_Const (Imm64 1w)));
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Const (Imm64 2w))) ]
    ;
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val core2_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "x1" (BType_Imm Bit64))
                  (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
                   Bit8);
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Den (BVar "x1" (BType_Imm Bit64))));
                   ];
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val set_env1_def = Define‘
      set_env1 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env; bst_prom := []|>
’;
val set_env2_def = Define‘
      set_env2 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env |>
’;


val core1_st = “set_env1 (bir_state_init ^core1_prog)”;
val core2_st = “set_env2 (bir_state_init ^core2_prog)”;

(* core definitions *)
val cores = “[(Core 0 ^core1_prog ^core1_st);
              (Core 1 ^core2_prog ^core2_st)]”;

val term_EVAL = rand o concl o EVAL ;

val final_states = term_EVAL “eval_promising 4 (^cores, [])”;

val _ = export_theory();
