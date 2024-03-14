"bir_arm8_backlifterTheory.bir_is_lifted_prog_MULTI_STEP_EXEC_compute"


bmr_rel r bs ms
?bs, precond? postcond under precond?

bir_lifting_machinesTheory.bmr_rel_def

bir_arm8_backlifterTheory.bir_pre_arm8_to_bir_def
bir_arm8_backlifterTheory.bir_post_bir_to_arm8_def


***** number of addr label steps (c_addr_labels?), but n' is the number of bir steps??? *****
(bir_exec_to_addr_label_n p bs n' = BER_Ended lo c_st c_addr_labels bs')
bir_inst_liftingTheory.bir_exec_to_addr_label_n_def
bir_inst_liftingTheory.bir_exec_to_addr_label_def
bir_programTheory.bir_exec_to_labels_n_def
bir_programTheory.bir_exec_to_labels_def

bir_programTheory.bir_exec_steps_GEN_def
bir_programTheory.bir_exec_infinite_steps_COUNT_STEPS_def
bir_programTheory.bir_exec_infinite_steps_fun_def
bir_programTheory.bir_exec_infinite_steps_fun_COUNT_PCs_def
bir_programTheory.bir_state_COUNT_PC_def

bir_wm_instTheory.bir_label_jgmt_impl_weak_jgmt

bir_htTheory.bir_exec_to_labels_triple_def

bir_program_terminationTheory???


!!!! ~bir_state_is_terminated, before and after !!!!






bir_arm8_backlifterTheory.arm8_triple_def

abstract_hoare_logicTheory.abstract_jgmt_def
abstract_simp_hoare_logicTheory.abstract_simp_jgmt_def

bir_arm8_backlifterTheory.arm_weak_model_def
bir_arm8_backlifterTheory.arm_weak_trs_def

bir_wm_instTheory.bir_simp_jgmt_def
bir_wm_instTheory.bir_etl_wm_def
bir_wm_instTheory.bir_weak_trs_def
bir_wm_instTheory.bir_exec_to_labels_triple_precond_def
