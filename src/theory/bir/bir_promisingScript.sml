open HolKernel Parse boolLib bossLib;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
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

val mem_default_value_def = Define‘mem_default_value = BVal_Imm (Imm1 0w)’;

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
  mem_read M l 0 = SOME mem_default_value
∧ mem_read M l t = case oEL t M of
                     NONE => NONE
                   | SOME msg => if msg.loc = l then SOME msg.val else NONE
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

(* core steps that don't affect memory *)
val (bir_cstep_rules, bir_cstep_ind, bir_cstep_cases) = Hol_reln`
(* read *)
(!p s s' v a_e M l (t:num) v_pre v_post v_addr var (a:num) (rk:num) mem_e en ty cid. (*TODO fix type of a and rk *)
   (bir_get_current_statement p s.bst_pc =
   SOME (BStmtB (BStmt_Assign var (BExp_Load mem_e a_e en ty)))
 ∧ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 ∧ mem_read M l t = v
 ∧ v_pre = MAX v_addr s.bst_v_rNew
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX ν_pre (s.bst_coh l))) ⇒ (EL t' M).loc ≠ l)
 ∧ v_post = MAX v_pre (mem_read_view a rk (s.bst_fwdb(l)) t)
 ∧ s' = s with <| bst_viewenv updated_by (λe. FUPDATE e (var,v_addr));
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_pc updated_by bir_pc_next |>)
 ==>
  cstep p cid s M [] s')
/\ (* fulfil *)
(!p s s' M v a_e l (t:num) v_pre v_post v_addr v_data var mem_e en v_e cid.
    ((bir_get_current_statement p s.bst_pc =
      SOME (BStmtB (BStmt_Assign var (BExp_Store mem_e a_e en v_e))))
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
 /\ t ∈ s.bst_prom
 /\ EL t M = <| loc := l; val := v; cid := cid  |>
 /\ v_pre = MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP))
 /\ (MAX v_pre (s.bst_coh l) < t)
 /\ v_post = t
 /\ s' = s with <| bst_prom updated_by (\pr. pr DIFF {t});
                   bst_coh := (\lo. if lo = l
                                    then MAX (s.bst_coh l) v_post
                                    else s.bst_coh(lo));
                   bst_v_wOld := MAX s.bst_v_wOld v_post;
                   bst_v_CAP := MAX s.bst_v_CAP v_addr;
                   bst_fwdb := (\lo. if lo = l
                                     then <| time := t;
                                             view := MAX v_addr v_data;
                                             xcl := false |>
                                     else s.bst_fwdb(lo));
                   bst_pc updated_by bir_pc_next |>)
 ==>
  cstep p cid s M [t] s')
/\ (* fence *)
(!p s s' M cid v.
   (((bir_get_current_statement p s.bst_pc =
     SOME (BStmtB BStmt_Fence)))
   /\ v = MAX s.bst_v_rOld s.bst_v_wOld
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew v;
                     bst_v_wNew := MAX s.bst_v_wNew v;
                     bst_pc updated_by bir_pc_next |>)
==>
  cstep p cid s M [] s')

(*/\ (* branch *)*)
(*/\ (* BIR single step *)*)
`;

val _ = export_theory();
