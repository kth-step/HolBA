open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open bir_mem_coreTheory;
open monadsyntax;
open alistTheory;

val _ = new_theory "bir_multicore";

(* ------------------------------------------------------------------------- *)
(*  Nondeterministic step relation with pipelining                           *)
(* ------------------------------------------------------------------------- *)

val next_stmt_def = Define`
next_stmt s = case s.bst_inflight of
        [] => NONE
      | ((BirInflight t0 stm)::stms) => SOME (t0,stm)
`;

val (bir_pstep_rules, bir_pstep_ind, bir_pstep_cases) = Hol_reln `
   (!p s1 s2 stm oo. ((next_stmt s1 = SOME (t0,stm))
                   /\ (bir_exec_stmt p stm s1 = (oo,s2)))
    ==> pstep p s1 (s2 with bst_inflight updated_by (remove_inflight t0)))

/\ (!p s1 stm istm.  ((bir_get_current_statement p s1.bst_pc = SOME stm)
                             /\ (istm = BirInflight (fresh s1) stm))
     ==> pstep p s1 (s1 with <| bst_inflight updated_by (APPEND [istm]);
                     bst_pc updated_by bir_pc_next;
                     bst_counter updated_by (\n:num.n+1) |>)
   )
`;

val bir_next_fetch_def = Define`
    bir_next_fetch p s =
       case bir_get_current_statement p s.bst_pc of
           NONE => []
           | SOME stm =>
             [ s with <| bst_inflight updated_by (APPEND [BirInflight (fresh s) stm]);
               bst_pc updated_by bir_pc_next; bst_counter updated_by (\n:num.n+1) |> ]
`;

val bir_next_exec_def = Define`
    bir_next_exec p s =
       case next_stmt s of
           NONE => []
         | SOME (t0,stm) => [ SND (bir_exec_stmt p stm s) with
                              <| bst_inflight updated_by (remove_inflight t0); |> ]
`;

val bir_compute_next_def = Define`
bir_compute_next p s =
   bir_next_fetch p s ++ bir_next_exec p s
`;

val bir_compute_steps_defn = Hol_defn "bir_compute_steps" `
bir_compute_steps (n:num) p s = if n = 0
                          then [s]
                          else LIST_BIND (bir_compute_next p s) (\s2. bir_compute_steps (n-1) p s2)
`;

(* Defn.tgoal bir_compute_steps_defn *)
val (bir_compute_steps_def, bir_compute_steps_ind) = Defn.tprove (bir_compute_steps_defn,
WF_REL_TAC `measure (\ (n,_,_). n)`);

val bir_next_states_def = Define`
bir_next_states p s =
  { s2 | pstep p s s2 }
`;

val (is_trace_rules, is_trace_ind, is_trace_cases)  = Hol_reln `
(!p s. is_trace p [s]) /\
(!p s2 s1 t . ((is_trace p (APPEND t [s1])) /\ (pstep p s1 s2))
    ==> (is_trace p (APPEND t [s1;s2])))
`;

val bir_traces_def = Define`
bir_traces p = { t | is_trace p t }
`;


(* ------------------------------------------------------------------------- *)
(*  Parallel evaluation                                                      *)
(* ------------------------------------------------------------------------- *)

val sys_st_def = Datatype`
    sys_st = core num (string bir_program_t) bir_state_t
           | mem mem_state_t 
`;

val exp_is_load_def = Define`
(exp_is_load (BExp_Load _ _ _ _) = T)
/\ (exp_is_load _ = F)
`;

val is_mem_def = Define`
(is_mem (BVar "MEM" _) = T)
/\ (is_mem _ = F)
`;

val next_is_atomic_def = Define`
(next_is_atomic p s =
 case (bir_get_program_block_info_by_label p (s.bst_pc.bpc_label)) of
     NONE => F
   | SOME (i,blk) => blk.bb_atomic)
`;

val (parstep_rules, parstep_ind, parstep_cases) = Hol_reln`
(!p s system m cid. (core cid p s) ∈ system
                 /\ (mem m) ∈ system
                 /\ next_is_atomic p s
                 /\ m.bmst_lock = NONE
                 /\ m' = m with <| bmst_lock := SOME cid |>
   ==> parstep system (system DIFF {mem m} UNION {mem m'}))
/\ (!p s system m t0 cid stm. (core cid p s) ∈ system
                 /\ (mem m) ∈ system
                 /\ m.bmst_lock = SOME cid
                 /\ (next_stmt s = SOME (t0,stm))
                 /\ (?end_stmt . stm = BStmtE end_stmt)
                 /\ m' = m with <| bmst_lock := NONE |>
    ==> parstep system (system DIFF {mem m} UNION {mem m'}))
/\ (!p s s' system. pstep p s s' /\ (core cid p s) ∈ system
   ==> parstep system (system DIFF {core cid p s} UNION {core cid p s'}))
/\ (!m m' system. memstep m m' /\ (mem m) ∈ system
   ==> parstep system (system DIFF {mem m} UNION {mem m'}))
/\ (!p s m m' s' t0 v ex system.
    ((core cid p s) ∈ system /\ (mem m) ∈ system
     /\ (next_stmt s = SOME (t0, (BStmtB (BStmt_Assign v ex))))
     /\ (m.bmst_lock = SOME cid)
     /\ (?t. v = BVar "MEM" t)
     /\ (m' = m with <| bmst_inflight updated_by
                (APPEND [BirInflight (memfresh m) (BStmtB (BStmt_Assign v ex))]);
                       bmst_counter updated_by (\n:num.n+1) |>)
     /\ (s' = s with bst_inflight updated_by (remove_inflight t0))
   ) ==>
   parstep system ((system DIFF {mem m} UNION {mem m'}) DIFF {core cid p s} UNION {core cid p s'}))
/\  (!p s s' v ex t0 value env' system.
     ((core cid p s) ∈ system /\ (mem m) ∈ system
      /\ (next_stmt s = SOME (t0, BStmtB (BStmt_Assign v ex)))
      /\ (m.bmst_lock = SOME cid)
      /\ (exp_is_load ex)
      /\ (SOME value = bir_eval_exp ex m.bmst_environ)
      /\ (SOME env' = bir_env_write v value s.bst_environ)
      /\ (s' = s with <| bst_inflight updated_by (remove_inflight t0);
                         bst_environ := env'  |>)
     ) ==>
    parstep system (system DIFF {core cid p s} UNION {core cid p s'}))
    `;


val compute_next_par_single_def = Define`
compute_next_par_single (core cid p s) m =
    LIST_BIND (bir_compute_next p s) (\s'. [(core cid p s', m)])
`;
val compute_next_par_mem_def = Define`
compute_next_par_mem c (mem m) =
    LIST_BIND (mem_compute_next m) (\m'. [(c, mem m')])
`;
val compute_next_store_def = Define`
compute_next_store (core cid p s) (mem m) =
    case next_stmt s of
         NONE => []
       | SOME (t0, BStmtB (BStmt_Assign v ex)) =>
         if is_mem v
         then (let m' = m with <| bmst_inflight updated_by
                             (APPEND [BirInflight (memfresh m) (BStmtB (BStmt_Assign v ex))]);
                  bmst_counter updated_by (\n:num.n+1) |>;
                  
              in let s' = s with bst_inflight updated_by (remove_inflight t0)
 in [(core cid p s', mem m')])
         else []
`;
val compute_next_load_def = Define`
compute_next_load (core cid p s) (mem m) =
              case next_stmt s of
                  NONE => []
                | SOME (t0, BStmtB (BStmt_Assign v ex)) =>
                  if exp_is_load ex
                  then case bir_eval_exp ex m.bmst_environ of
                       NONE => []
                       | SOME value =>
                       case bir_env_write v value s.bst_environ of
                           NONE => []
                           | SOME env' =>
                           (let s' = s with <| bst_inflight updated_by (remove_inflight t0);
                                bst_environ := env'  |>
                            in [(core cid p s', mem m)])
                  else []
`;

val update_core_def = Define`
    (update_core cid c [] = [(cid,c)]) 
/\  (update_core cid c ((x,y)::cores) =
     if cid = x
     then (x,c)::cores
     else (x,y)::update_core cid c cores)
`;

(* val _ = enable_monadsyntax(); *)
val compute_next_par_def = Define`
compute_next_par (cores:(num # sys_st) list, m) =
   LIST_BIND cores (\ (cid,c).
      LIST_BIND (APPEND (compute_next_par_single c m)
                           (APPEND (compute_next_par_mem c m)
                                   (APPEND (compute_next_load c m)
                                           (compute_next_store c m))))
                (\ (c',m') . [(update_core cid c' cores, m')]))
`;
                                       
val compute_next_par_steps_def = Define`
compute_next_par_steps (n:num) (cores:(num # sys_st) list, m) =
      if n = 0
      then [(cores,m)]
      else LIST_BIND (compute_next_par (cores,m)) (\s2. compute_next_par_steps (n-1) s2)
`;

val _ = export_theory ();
