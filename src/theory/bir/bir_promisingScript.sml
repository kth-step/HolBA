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
  bmst_lock        : num option;
  bmst_counter     : num;
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
mem_read_view a rk (f:fwdb_t) t = if f.time = t then f.view else t
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

(* Checks if the memory expressions from lifted loads and stores
 * refers to regular memory or dummy memory. May look inside casts *)
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
 * needed to apply the fulfil rule (can look inside one cast) *)
val get_fulfil_args_v_def = Define`
  (get_fulfil_args_v (BExp_Cast cast_ty v_e imm_ty) =
   case get_fulfil_args_v v_e of
   | SOME (v_e', NONE) => SOME (v_e', SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_fulfil_args_v (BExp_Den v) = SOME (BExp_Den v, NONE)) /\
  (get_fulfil_args_v _ = NONE)
`;
val get_fulfil_args_def = Define`
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) =
   case get_fulfil_args_v v_e of
   | SOME (v_e, NONE) => SOME (a_e, v_e, NONE)
   | SOME (v_e', SOME (cast_ty, imm_ty)) => SOME (a_e, v_e', SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_fulfil_args _ = NONE)
`;

(* TODO: "Generalising variable "ν_pre" in clause #0 (113:1-131:23)"? *)
(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v e a_e cast_opt M l (t:num) v_pre v_post v_addr var (a:num) (rk:num) new_env cid. (*TODO fix type of a and rk *)
   (bir_get_current_statement p s.bst_pc =
   SOME (BStmtB (BStmt_Assign var e))
 /\ get_read_args e = SOME (a_e, cast_opt)
 ∧ ~(contains_dummy_mem e)
 ∧ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
(* TODO: Not working, since the read value needs to be cast
 * (consider the typical case of signed casts from 32 to 64 bits).
 * Also, endianness? (should be OK for RISC-V) *)
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
(!p s s' M v e a_e cast_opt l (t:num) v_pre v_post v_addr v_data var v_e cid.
    ((bir_get_current_statement p s.bst_pc =
      SOME (BStmtB (BStmt_Assign var e)))
 /\ get_fulfil_args e = SOME (a_e, v_e, cast_opt)
 /\ ~(contains_dummy_mem e)
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
/\ (* branch (conditional jump) *)
(!p s s' M cid v oo s2 v_addr cond_e lbl1 lbl2 stm.
   (bir_get_current_statement p s.bst_pc = SOME stm
    /\ stm = BStmtE (BStmt_CJmp cond_e lbl1 lbl2)
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
    /\ bir_exec_stmt p stm s = (oo,s2)
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr;
                       bst_xcl := false |>)
(* Use bir_get_program_block_info_by_label *)
==>
  clstep p cid s M [] s')
/\ (* branch (jump) *)
(!p s s' M cid oo s2 lbl stm.
   (bir_get_current_statement p s.bst_pc = SOME stm
    /\ stm = BStmtE (BStmt_Jmp lbl)
    /\ bir_exec_stmt p stm s = (oo,s2)
    /\ s' = s2 with <| bst_xcl := false |>)
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
Core num (string bir_program_t) bir_state_t
`;

(* system step *)
val (bir_parstep_rules, bir_parstep_ind, bir_parstep_cases) = Hol_reln`
(!p cid s s' M M' cores prom.
   (Core cid p s ∈ cores
    /\ cstep p cid s M prom s' M'
    /\ is_certified p cid s' M')
==>
   parstep cores M (cores DIFF {Core cid p s} UNION {Core cid p s'}) M')
`;

val env_update_cast64_def = Define‘
  env_update_cast64 varname (BVal_Imm v) vartype env =
    bir_env_update varname (BVal_Imm (n2bs (b2n v) Bit64)) vartype env
’;

(* Core-local execution *)
(* TODO: Does this have redundant parameters? *)
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

(* TODO: Does this have redundant parameters? *)
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

(* TODO: Redundant parameters *)
val eval_clstep_fence_def = Define‘
  eval_clstep_fence p cid s M =
  let v = MAX s.bst_v_rOld s.bst_v_wOld
  in
    [s with <| bst_v_rNew := MAX s.bst_v_rNew v;
               bst_v_wNew := MAX s.bst_v_wNew v;
               bst_pc updated_by bir_pc_next |>]
’;

(* TODO: Redundant parameters *)
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

val eval_clstep_exp_def = Define‘
  eval_clstep_exp p cid s M var ex =
  case bir_eval_exp_view ex s.bst_environ s.bst_viewenv
  of (SOME val, v_val) =>
       (case env_update_cast64 (bir_var_name var) val (bir_var_type var) (s.bst_environ) of
          SOME new_env =>
            [s with <| bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                       bst_environ := new_env;
                       bst_pc updated_by bir_pc_next |>]
        | _ => [])
  | _ => []
’;

(* TODO: Redundant parameters *)
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
   | SOME (BStmtB (BStmt_Assign var ex)) =>
       eval_clstep_exp p cid s M var ex
   | SOME stm =>
       eval_clstep_bir_step p cid s M stm
   | _ => []
’;


(*** Certify execution execution ***)
Definition eval_certify_def:
  (
  eval_certify p cid s M 0 =
  NULL s.bst_prom
  ) /\ (
  eval_certify p cid s M (SUC fuel) =
  (NULL s.bst_prom \/
   EXISTS (\s'. eval_certify p cid s' M fuel)
          (eval_clstep p cid s M))
  )
End

(*** Non-promising-mode execution ***)
Definition eval_clstep_core:
  eval_clstep_core M (Core cid p s) =
  MAP (Core cid p) (eval_clstep p cid s M)
End

Definition eval_clsteps_aux_def:
  (
  eval_clsteps_aux 0 M core = [core]
  ) /\ (
  eval_clsteps_aux (SUC f) M core = 
  LIST_BIND (eval_clstep_core M core)
            (eval_clsteps_aux f M)
  )
End

(* Cartesian product for list *)
Definition CART_PROD_LIST_def:
  (
  CART_PROD_LIST [] = [[]]
  ) /\ (
  CART_PROD_LIST (l::ll) =
    LIST_BIND l (\h. MAP (\l'. h::l') (CART_PROD_LIST ll))
  )
End

Definition eval_clsteps_def:
eval_clsteps f (cores, M) =
let
  cores_list = CART_PROD_LIST $ MAP (eval_clsteps_aux f M) cores
in
  MAP (\cores. (cores, M)) cores_list
End

(*** Promsing-mode execution ***)
Definition eval_find_promises_def:
  (
  eval_find_promises p cid s M promises t 0 =
  if NULL s.bst_prom then promises else []
  ) ∧ (
  eval_find_promises p cid s M promises t (SUC f) =
  (case bir_get_current_statement p s.bst_pc of
     SOME (BStmtB (BStmt_Assign _ (BExp_Store _ a_e _ v_e))) =>
       (let
          (sl, v_loc) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
          (sv, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
          msg = <| loc := THE sl; val := THE sv; cid := cid |>;
          v_pre = MAX v_loc $ MAX v_data $ MAX s.bst_v_CAP s.bst_v_wNew;
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
End

Definition eval_pstep:
  eval_pstep p cid s M ff =
  let
    t = LENGTH M + 1;
    promises = nub $ eval_find_promises p cid s M [] t ff;
    s' = s with <| bst_prom updated_by (CONS t) |> 
  in
    MAP (λp. (s', SNOC p M)) promises
End

Definition eval_pstep_core:
  eval_pstep_core ff M (Core cid p s) =
  MAP (λsM. (Core cid p (FST sM), SND sM))
      (eval_pstep p cid s M ff)
End

Definition update_core_def:
  (
  update_core new_c [] = []
  ) ∧ (
  update_core (Core new_cid new_p new_st) (Core cid p st::cs) =
  if new_cid = cid then
    Core new_cid new_p new_st :: cs
  else
    Core cid p st :: update_core (Core new_cid new_p new_st) cs
  )
End

Definition eval_psteps_def:
  (
  eval_psteps ff 0 (cores, M) = [(cores, M)]
  ) ∧ (
  eval_psteps ff (SUC f) (cores, M) =
  case LIST_BIND cores (eval_pstep_core ff M) of
    [] => [(cores,M)]
  | cMs => LIST_BIND (MAP (\cM. (update_core (FST cM) cores, SND cM)) cMs)
                     (eval_psteps ff f)
  )
End

(*** Combined Promising and Non-Promising executions. ***)
Definition eval_promising:
  eval_promising fuel (cores, M) =
  LIST_BIND (eval_psteps fuel fuel (cores, M))
            (eval_clsteps fuel)
End

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
