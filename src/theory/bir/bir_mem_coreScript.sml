open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_programTheory;

val _ = new_theory "bir_mem_core";

(* ------------------------------------------------------------------------- *)
(*  Memory                                                                   *)
(* ------------------------------------------------------------------------- *)

val mem_state_def = Datatype`
mem_state_t = <|
  bmst_environ  : bir_var_environment_t;
(*  bmst_status   : bir_status_t; *)
  bmst_lock     : num option;
  bmst_counter  : num;
  bmst_inflight : (num # string bir_inflight_stmt_t) list
  |>
`;

val memfresh_def = Define`
memfresh s = STRCAT "mt" (n2s s.bmst_counter)
`;


val next_memop_def = Define`
next_memop s = case s.bmst_inflight of
                   [] => NONE
                 | ((cid,BirInflight t0 stm)::stms) => SOME (t0,stm)
`;

val commit_memop_def = Define`
commit_memop (BStmtB (BStmt_Assign v ex)) s =
case bir_eval_exp ex s.bmst_environ of
     | SOME va =>
            (case bir_env_write v va s.bmst_environ of
                  | SOME env => (s with bmst_environ := env)
                  | NONE => ARB)
     | NONE => ARB
`;

val memflush_def = Define`
   (memflush target_cid [] s = s)
/\ (memflush target_cid ((cid,BirInflight t0 stm)::stms) s =
    if cid = target_cid
    then memflush target_cid stms (commit_memop stm s)
    else memflush target_cid stms s)
`;

val remove_mem_inflight_def = Define`
remove_mem_inflight t l =
   FILTER (\bi . case bi of (_,BirInflight t0 _) => (t <> t0)) l
`;

val (memstep_rules, memstep_ind, memstep_cases) = Hol_reln`
(!s1 s2 stm. ((next_memop s1 = SOME (t0,stm))
              /\ (commit_memop stm s1 = s2))
     ==> memstep s1 (s2 with bmst_inflight updated_by (remove_mem_inflight t0)))
`;

val mem_compute_next_def = Define`
    mem_compute_next ms =
        case next_memop ms of
            NONE => []
          | SOME (t0,stm) =>
            [commit_memop stm ms with bmst_inflight updated_by (remove_mem_inflight t0)]
`;

val mem_init_def = Define`
mem_init =
<| bmst_environ  := bir_env_default (bir_envty_of_vs {});
   bmst_counter  := 0;
   bmst_lock     := NONE;
   bmst_inflight := []
|>`;


val _ = export_theory ();

