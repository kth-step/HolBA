open HolKernel Parse boolLib bossLib;

(* Theories from theory/bir: *)
open bir_programTheory bir_typing_progTheory bir_envTheory
     bir_auxiliaryTheory bir_valuesTheory bir_expTheory
     bir_exp_immTheory bir_typing_expTheory bir_immTheory;

(* Theories from theory/bir-support: *)
open bir_program_blocksTheory bir_program_terminationTheory
     bir_program_valid_stateTheory bir_exp_substitutionsTheory
     bir_bool_expTheory bir_program_env_orderTheory
     bir_program_multistep_propsTheory bir_exp_equivTheory
     bir_subprogramTheory bir_program_no_assumeTheory;

(* Local theories: *)
open bir_wpTheory;

(* Simplification sets from theory/bir: *)
open HolBACoreSimps;

(* This theory contains theorems for manipulation of Hoare
 * triples not directly related to WP propagation. *)
val _ = new_theory "bir_ht";

val bir_exec_to_labels_triple_def = Define `
  bir_exec_to_labels_triple p l ls pre post =
  !s r.
    bir_env_vars_are_initialised s.bst_environ
                                 (bir_vars_of_program p) ==>
    ((s.bst_pc.bpc_index = 0) /\ (s.bst_pc.bpc_label = l)) ==>
    (s.bst_status = BST_Running) ==>
    bir_is_bool_exp_env s.bst_environ pre ==>
    (bir_eval_exp pre (s.bst_environ) = SOME bir_val_true) ==>
    ((bir_exec_to_labels ls p s) = r) ==>
    (?l1 c1 c2 s'.
      (r = BER_Ended l1 c1 c2 s') /\
      (s'.bst_status = BST_Running) /\
      bir_is_bool_exp_env s'.bst_environ (post s'.bst_pc.bpc_label) /\
      (bir_eval_exp (post s'.bst_pc.bpc_label) s'.bst_environ = SOME bir_val_true) /\
      ((s'.bst_pc.bpc_index = 0) /\ (s'.bst_pc.bpc_label IN ls))
    )`;

val bir_never_assumviol_ht =
  store_thm("bir_never_assumviol_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_exec_to_labels_triple prog l ls pre post``,

REWRITE_TAC [bir_exec_to_labels_triple_def,
             bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s r. _``
            (fn thm => ASSUME_TAC
              (SPECL [``s:bir_state_t``,
                      ``r: 'a bir_execution_result_t``] thm)
            ) >>
Cases_on `r` >| [
  rename1 `bir_exec_to_labels ls prog s = BER_Ended l' n n0 s'` >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  subgoal `s.bst_status <> BST_AssumptionViolated` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] 
  ) >>
  Cases_on `bir_is_valid_pc prog s.bst_pc` >| [
    FULL_SIMP_TAC std_ss
                  [bir_is_valid_pc_def,
                   bir_get_program_block_info_by_label_def] >>
    subgoal `?bl. bir_get_current_block prog s.bst_pc = SOME bl`
      >- (
      FULL_SIMP_TAC std_ss [bir_get_current_block_def]
    ) >>
    IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_to_labels,

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
    subgoal `~bir_state_is_terminated s` >- (
      FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
    ) >>
    IMP_RES_TAC bir_state_is_failed_step_not_valid_pc >>
    Cases_on `n` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_REWR_0],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_step_n_SUC, bir_exec_step_state_def] >>
      Cases_on `(bir_exec_step prog s)` >>
      ASSUME_TAC (el 4 (CONJUNCTS bir_exec_step_n_REWRS)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_is_terminated_def, LET_DEF] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ]
  ],

  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

val _ = export_theory();
