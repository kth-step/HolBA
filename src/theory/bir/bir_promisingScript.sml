open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
open listRangeTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;

val _ = new_theory "bir_promising";

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val mem_msg_def = Datatype‘
mem_msg_t = <| loc : bir_val_t; val : bir_val_t; cid : num  |>
’;

val mem_def = Datatype`
mem_t = <|
  bmst_lock     : num option;
  bmst_counter  : num;
  bmst_storebuffer : mem_msg_t list;
|>
`;

val mem_default_value_def = Define‘mem_default_value = BVal_Imm (Imm64 0w)’;

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
mem_read_view a rk f t = if f.time = t then f.view else t
’;

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
val bir_eval_exp_view_def = Define‘
  (bir_eval_exp_view (BExp_BinExp et e1 e2) env viewenv =
  let (val1,v1) = bir_eval_exp_view e1 env viewenv
   in let (val2,v2) = bir_eval_exp_view e2 env viewenv
   in let  result = bir_eval_bin_exp et val1 val2
   in (result, MAX v1 v2))
∧ (bir_eval_exp_view (BExp_Den v) env viewenv =
   let res = bir_eval_exp (BExp_Den v) env
    in case FLOOKUP viewenv v of
       NONE => (res, 0)
     | SOME view => (res, view))
∧ bir_eval_exp_view exp env viewenv = (bir_eval_exp exp env, 0)
’;

Theorem bir_eval_exp_view_sound:
  ∀ exp env viewenv .
  ∃ y. (bir_eval_exp_view exp env viewenv) = (bir_eval_exp exp env,y)
Proof
 Induct
 >> fs [bir_eval_exp_view_def]
 >> REPEAT STRIP_TAC
 >| [Cases_on ‘FLOOKUP viewenv b’
     >| [EXISTS_TAC “0:num”,Q.EXISTS_TAC ‘x’]
    ,RULE_ASSUM_TAC SPEC_ALL
     >> fs []]
 >> EVAL_TAC
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

(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v a_e M l (t:num) v_pre v_post v_addr var (a:num) (rk:num) mem_e en new_env ty cid. (*TODO fix type of a and rk *)
   (bir_get_current_statement p s.bst_pc =
   SOME (BStmtB (BStmt_Assign var (BExp_Load mem_e a_e en ty)))
 ∧ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 ∧ mem_read M l t = SOME v
 ∧ v_pre = MAX v_addr s.bst_v_rNew
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX ν_pre (s.bst_coh l))) ⇒ (EL t' M).loc ≠ l)
 ∧ v_post = MAX v_pre (mem_read_view a rk (s.bst_fwdb(l)) t)
 /\ SOME new_env = bir_env_update (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 ∧ s' = s with <| bst_viewenv updated_by (λe. FUPDATE e (var,v_addr));
                  bst_environ := new_env;
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_pc updated_by bir_pc_next |>)
 ==>
  clstep p cid s M [] s')
/\ (* fulfil *)
(!p s s' M v a_e l (t:num) v_pre v_post v_addr v_data var mem_e en v_e cid.
    ((bir_get_current_statement p s.bst_pc =
      SOME (BStmtB (BStmt_Assign var (BExp_Store mem_e a_e en v_e))))
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
 /\ MEM t s.bst_prom
 /\ EL t M = <| loc := l; val := v; cid := cid  |>
 /\ v_pre = MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP))
 /\ (MAX v_pre (s.bst_coh l) < t)
 /\ v_post = t
 /\ s' = s with <| bst_prom updated_by (FILTER (\t'. t' ≠ t));
                   bst_coh := (\lo. if lo = l
                                    then MAX (s.bst_coh l) v_post
                                    else s.bst_coh(lo));
                   bst_v_wOld := MAX s.bst_v_wOld v_post;
                   bst_v_CAP := MAX s.bst_v_CAP v_addr;
                   bst_fwdb := (\lo. if lo = l
                                     then <| time := t;
                                             view := MAX v_addr v_data;
                                             xcl := F |>
                                     else s.bst_fwdb(lo));
                   bst_pc updated_by bir_pc_next |>)
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
/\ (* branch *)
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
(!p cid s M s'.
  clstep p cid s M ([]:num list) s'
==>
  cstep p cid s M [] s' M)

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
val is_certified_def = Define`
is_certified p cid s M = ?s' M'.
  cstep_seq_rtc p cid (s, M) (s', M')
  /\ s'.bst_prom = []
`;

val core_t_def = Datatype `core_t =
core num (string bir_program_t) bir_state_t
`;

(* system step *)
val (bir_parstep_rules, bir_parstep_ind, bir_parstep_cases) = Hol_reln`
(!p cid s s' M M' cores.
   (core cid p s ∈ cores
    /\ cstep p cid s M [] s' M'
    /\ is_certified p cid s' M')
==>
   parstep cores M (cores DIFF {core cid p s} UNION {core cid p s'}) M')
`;

val env_update_cast64_def = Define‘
  env_update_cast64 varname (BVal_Imm v) vartype env =
    bir_env_update varname (BVal_Imm (n2bs (b2n v) Bit64)) vartype env
’;

(* execution *)
val eval_clstep_read_def = Define‘
  eval_clstep_read p cid s M var mem_e a_e en ty =
   let (sl, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
       v_pre = MAX v_addr s.bst_v_rNew;
   in case sl of
        SOME l =>
       let t_max = MAX v_pre (s.bst_coh l);
           ts = FILTER (\t. EVERY (\t'. ((EL (t'-1) M).loc ≠ l)) [(t+1) .. t_max]) (0::mem_timestamps l M)
       in
         FLAT (MAP (\t.
                let sv = mem_read M l t;
                    v_post = MAX v_pre (mem_read_view 0 0 (s.bst_fwdb(l)) t);
                in
                 case sv of
                  SOME v =>
                    (case env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ) of
                       SOME new_env =>
                         [s with <| bst_viewenv updated_by (λe. FUPDATE e (var,v_addr));
                                    bst_environ := new_env;
                                    bst_coh := (λlo. if lo = l
                                                     then MAX (s.bst_coh l) v_post
                                                     else s.bst_coh(lo));
                                    bst_v_rOld := MAX s.bst_v_rOld v_post;
                                    bst_v_CAP := MAX s.bst_v_CAP v_addr;
                                    bst_pc updated_by bir_pc_next |>]
                     | _ => [])
                 | _ => [])
             ts)
         | _ => []
’;

val eval_clstep_fulfil_def = Define‘
  eval_clstep_fulfil p cid s M var mem_e a_e en v_e =
    let (sl, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
        (sv, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    in case (sl,sv) of
       (SOME l, SOME v) =>
       let v_pre =  MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP));
           ts = FILTER (\t. (EL (t-1) M = <| loc := l; val := v; cid := cid  |>)
                            /\ (MAX v_pre (s.bst_coh l) < t)) (s.bst_prom);
       in MAP (\v_post. s with <| bst_prom updated_by (FILTER (\t'. t' ≠ v_post));
                                  bst_coh := (\lo. if lo = l
                                                   then MAX (s.bst_coh l) v_post
                                                   else s.bst_coh(lo));
                                  bst_v_wOld := MAX s.bst_v_wOld v_post;
                                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                                  bst_fwdb := (\lo. if lo = l
                                                    then <| time := v_post;
                                                            view := MAX v_addr v_data;
                                                            xcl := F |>
                                                    else s.bst_fwdb(lo));
                                  bst_pc updated_by bir_pc_next |>)
              ts
          | _ => []
’;

val eval_clstep_fence_def = Define‘
  eval_clstep_fence p cid s M =
  let v = MAX s.bst_v_rOld s.bst_v_wOld
  in
    [s with <| bst_v_rNew := MAX s.bst_v_rNew v;
               bst_v_wNew := MAX s.bst_v_wNew v;
               bst_pc updated_by bir_pc_next |>]
’;

val eval_clstep_branch_def = Define‘
  eval_clstep_branch p cid s M stm =
  case stm of
    BStmtE (BStmt_CJmp cond_e lbl1 lbl2) =>
      let (sv, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
      in
        case sv of
          SOME v =>
            let (oo,s2) = bir_exec_stmt p stm s
            in [s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>]
’;

val eval_clstep_bir_step_def = Define‘
  eval_clstep_bir_step p cid s M stm =
   let (oo,s') = bir_exec_stmt p stm s
   in [s']
’;

val eval_clstep_def = Define‘
   eval_clstep p cid s M =
   case bir_get_current_statement p s.bst_pc of
     SOME (BStmtB (BStmt_Assign var (BExp_Load mem_e a_e en ty))) =>
       eval_clstep_read p cid s M var mem_e a_e en ty
   | SOME (BStmtB (BStmt_Assign var (BExp_Store mem_e a_e en v_e))) =>
       eval_clstep_fulfil p cid s M var mem_e a_e en v_e 
   | SOME (BStmtB (BStmt_Fence BM_ReadWrite BM_ReadWrite)) =>
       eval_clstep_fence p cid s M
   | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
       eval_clstep_branch p cid s M (BStmtE (BStmt_CJmp cond_e lbl1 lbl2))
   | SOME stm =>
       eval_clstep_bir_step p cid s M stm
   | _ => []
’;

val eval_clstep_core_def = Define‘
  eval_clstep_core M (core cid p st) = MAP (core cid p) (eval_clstep p cid st M)
’;

  
val eval_parstep_def = Define‘
   eval_parstep cores M =
      (MAP (eval_clstep_core M) cores)
’;

val update_core_def = Define‘
   update_core new_c [] = []
/\ update_core (core new_cid new_p new_st) (core cid p st::cs) =
     if new_cid = cid
     then core new_cid new_p new_st :: cs
     else core cid p st :: update_core (core new_cid new_p new_st) cs
’;

val core_is_halted_def = Define‘
   core_is_running (core cid p st) = (st.bst_status = BST_Running)
’;

val eval_parsteps_def = Define‘
   eval_parsteps 0       cores M = [cores]
/\ eval_parsteps (n:num) cores M =
     LIST_BIND (FILTER core_is_running cores) (\c.
       LIST_BIND (eval_clstep_core M c) (\c'. let cores' = update_core c' cores in
                                                eval_parsteps (n-1) cores' M))
’;

(* examples *)
val core1_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
     (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
      (BExp_Const (Imm8 1w)));
     BStmt_Assign (BVar "x2" (BType_Imm Bit64))
                  (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x1" (BType_Imm Bit64))) BEnd_LittleEndian
                   Bit8)];
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val core2_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_statements :=
    [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
     (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x1" (BType_Imm Bit64))) BEnd_LittleEndian
      (BExp_Const (Imm8 1w)));
     BStmt_Assign (BVar "x2" (BType_Imm Bit64))
                  (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x0" (BType_Imm Bit64))) BEnd_LittleEndian
                   Bit8)];
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

(* BIR quotations
core0_prog =
BIR
`start:
MEM=MEM{x0 := 1}
x2=MEM[x1]
halt x2`;

core1_prog =
BIR
‘start:
MEM=MEM{x1 := 1}
x2=MEM[x0]
halt x2’;
*)

val bir_eval_exp_store_msg_def = Define‘
 bir_eval_exp_store_msg ex env cid =
   case ex of
     BExp_Store mem_e a_e en v_e =>
      (let mem_v = bir_eval_exp mem_e env;
           a_v = bir_eval_exp a_e env;
           va = bir_eval_exp v_e env
       in
         case bir_eval_store mem_v a_v en va of
           SOME mem' => SOME (<| loc := THE a_v; val := THE va; cid := cid |>, mem')
           | _ => NONE)
   | _ => NONE
’;
val bir_exec_step_msg_def = Define‘
  bir_exec_step_msg p cid st M =
    if (bir_state_is_terminated st) then (NONE, st)
    else
      case (bir_get_current_statement p st.bst_pc) of
      | NONE => (NONE, bir_state_set_failed st)
      | SOME (BStmtB (BStmt_Assign v ex)) =>
          (case ex of
            BExp_Store mem_e a_e en v_e =>
              (case bir_eval_exp_store_msg ex st.bst_environ cid of
                SOME (msg,va) =>
                  (case bir_env_write v va st.bst_environ of
                     SOME env => (SOME msg, st with <| bst_environ := env; bst_pc updated_by bir_pc_next |>)
                    | NONE => (NONE, bir_state_set_typeerror st))
                | NONE => (NONE, bir_state_set_typeerror st))
           | _ =>
               (case eval_clstep p cid st M of
                 st'::_ => (NONE,st')
                 | [] => (NONE, st)))
      | SOME stm => case eval_clstep p cid st M of
                      st'::_ => (NONE,st')
                      | [] => (NONE, st)
’;

val bir_exec_steps_msg_def = Define ‘
                              bir_exec_steps_msg p cid 0 st M = ([],st)
                              /\ bir_exec_steps_msg p cid (n:num) st M =
                                 case bir_exec_step_msg p cid st M of
                                   (msg_opt,st') =>
                                     case bir_exec_steps_msg p cid (n-1) st' M of
                                       (ms,st'') => ((case msg_opt of
                                                        SOME msg => msg::ms
                                                      | NONE => ms), st'')
                             ’;


val set_env_defaults_def = Define‘
      set_env_defaults s =
         let env = BEnv (\v. case v of
                               "x0" => SOME (BVal_Imm (Imm64 0w))
                             | "x1" => SOME (BVal_Imm (Imm64 4w))
                             | "x2" => SOME (BVal_Imm (Imm64 8w))
                             | "MEM" => SOME (BVal_Mem Bit64 Bit8 (FUN_FMAP (\x. 0) (\(x:num).T)))
                             | _ => NONE)
         in s with <| bst_environ := env; |>
’;

fun term_EVAL tm = (rand o concl) (EVAL tm);
val core_promises_def = Define‘
  core_promises n (core cid prog st) = FST (bir_exec_steps_msg prog cid n st [])
’;

val core1_st = term_EVAL “set_env_defaults (bir_state_init ^core1_prog)”;
val core2_st = term_EVAL “set_env_defaults (bir_state_init ^core2_prog)”;

(* core definitions *)
val cores = “[(core 0 ^core1_prog ^core1_st);
              (core 1 ^core2_prog ^core2_st)]”;

(* 'promising'-mode per-core execution *)
val promised_mem = term_EVAL “FLAT (MAP (core_promises 2) ^cores)”;
val promised_mem2 = term_EVAL “case ^promised_mem of [a;b] => [b;a]”;

fun core_st_promised n st promises = term_EVAL “^st with <| bst_prom := [(^n)] |>”;
val core1_st_promised = core_st_promised “1:num” core1_st promised_mem;
val core2_st_promised = core_st_promised “2:num” core2_st promised_mem;
val core1_st_promised2 = core_st_promised “2:num” core1_st promised_mem2;
val core2_st_promised2 = core_st_promised “1:num” core2_st promised_mem2;

val cores_promised = “[(core 0 ^core1_prog ^core1_st_promised);
                       (core 1 ^core2_prog ^core2_st_promised)]”;
val cores_promised2 = “[(core 0 ^core1_prog ^core1_st_promised2);
                        (core 1 ^core2_prog ^core2_st_promised2)]”;

val inspect_trace_def = Define‘
  inspect_trace cores =
      MAP (\c. case c of core cid p st => (cid, bir_env_lookup "x2" st.bst_environ)) cores
’;

(* 'non-promising'-mode execution *)
val traces = term_EVAL “MAP inspect_trace (eval_parsteps 7 ^cores_promised ^promised_mem)”;
val traces2 = term_EVAL “eval_parsteps 3 ^cores_promised2 ^promised_mem2”;

val core_step1 = term_EVAL “HD (eval_clstep_core ^promised_mem (HD ^cores_promised))”;
val test2 = term_EVAL “LIST_BIND (eval_clstep_core ^promised_mem (HD ^cores_promised)) (\c. eval_clstep_core ^promised_mem c)”;

val _ = export_theory();
