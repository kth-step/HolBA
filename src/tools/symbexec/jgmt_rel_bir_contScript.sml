open HolKernel boolLib Parse bossLib;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_htTheory;
open symb_prop_transferTheory
open bir_program_transfTheory;

val _ = new_theory "jgmt_rel_bir_cont";

Theorem abstract_jgmt_rel_bir_cont:
 !bprog l ls pre post.
  ls <> {} ==>
   abstract_jgmt_rel (bir_ts bprog) l ls
    (\st. bir_exec_to_labels_triple_precond st pre bprog)
    (\st st'. bir_exec_to_labels_triple_postcond st' post bprog) ==>
   bir_cont bprog bir_exp_true l ls {} pre post
Proof
 rw [abstract_jgmt_rel_def,bir_cont_def] >>
 rw [t_ext_jgmt_def] >>
 rw [t_jgmt_def] >>
 `?st'. (bir_ts bprog).weak ls s st' ∧
   bir_exec_to_labels_triple_postcond st' post bprog`
  by METIS_TAC [] >>
 Q.EXISTS_TAC `st'` >> 
 fs [bir_exec_to_labels_triple_precond_def] >>
 rw [bir_eval_exp_TF,bir_is_bool_exp_env_REWRS] >>
 fs [bir_exec_to_labels_triple_postcond_def]
QED

Theorem bir_exec_to_labels_triple_precond_exp_true:
 !st pre bprog.
  bir_exec_to_labels_triple_precond st pre bprog ==>
  bir_exec_to_labels_triple_precond st bir_exp_true bprog
Proof
 rw [bir_exec_to_labels_triple_precond_def,
  bir_eval_exp_TF,bir_is_bool_exp_env_REWRS]
QED

Theorem bir_cont_abstract_jgmt_rel:
 !bprog l ls pre post.
   bir_cont bprog bir_exp_true l ls {} pre post ==>
   abstract_jgmt_rel (bir_ts bprog) l ls
    (\st. bir_exec_to_labels_triple_precond st pre bprog)
    (\st st'. bir_exec_to_labels_triple_postcond st' post bprog) 
Proof
 rw [abstract_jgmt_rel_def,bir_cont_def,t_ext_jgmt_def,t_jgmt_def] >> 
 METIS_TAC [bir_exec_to_labels_triple_precond_exp_true]
QED

Theorem abstract_jgmt_rel_thm_precond:
 !st pre bprog. 
  bir_exec_to_labels_triple_precond st pre bprog ==>
  st.bst_pc.bpc_index = 0
Proof
 rw [bir_exec_to_labels_triple_precond_def]
QED

Theorem abstract_jgmt_rel_thm_postcond:
 !ls st post bprog. 
  bir_exec_to_labels_triple_postcond st post bprog ==>
  ~ bir_state_is_terminated st
Proof
 rw [bir_exec_to_labels_triple_postcond_def] >>
 rw [bir_state_is_terminated_def]
QED

val _ = export_theory ();
