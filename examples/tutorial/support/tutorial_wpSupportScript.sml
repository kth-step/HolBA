open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open easy_noproof_wpLib;
open bir_wpTheory bir_htTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples: *)
open tutorial_bir_to_armSupportTheory bir_program_no_assumeTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorial_wpSupport";

val bir_exec_to_labels_exists =
  store_thm("bir_exec_to_labels_exists",
  ``!ls prog st.
      ?r.
        bir_exec_to_labels ls prog st = r``,

FULL_SIMP_TAC std_ss [bir_exec_to_labels_def]
);


val bir_never_assumviol_block_n_ht_from_to_labels_ht =
  store_thm("bir_never_assumviol_block_n_ht_from_to_labels_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_triple prog l ls pre post``,

REWRITE_TAC [bir_triple_def,
             bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``ls:bir_label_t -> bool``,
                   ``prog:'a bir_program_t``,
                   ``s:bir_state_t``] bir_exec_to_labels_exists) >>
FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``!s'. _``
            (fn thm => ASSUME_TAC
              (SPEC ``s:bir_state_t`` thm)
            ) >>
REV_FULL_SIMP_TAC std_ss [] >| [
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
  IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
  quantHeuristicsLib.QUANT_TAC [("n", `m`, []),
				("l1", `l1`, []),
				("c1", `c1`, []),
				("c2", `c_l'`, []),
				("s'", `s'`, [])] >>
  FULL_SIMP_TAC std_ss [],

  Cases_on `bir_is_valid_pc prog s.bst_pc` >| [
    FULL_SIMP_TAC std_ss
                  [bir_is_valid_pc_def,
                   bir_get_program_block_info_by_label_def] >>
    subgoal `?bl. bir_get_current_block prog s.bst_pc = SOME bl`
      >- (
      FULL_SIMP_TAC std_ss [bir_get_current_block_def]
    ) >>
    subgoal `s.bst_status <> BST_AssumptionViolated` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] 
    ) >>
    IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_to_labels,

    (* This part is admittedly a bit of a yarn *)
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
    subgoal `~bir_state_is_terminated s` >- (
      FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
    ) >>
    IMP_RES_TAC bir_state_is_failed_step_not_valid_pc >>
    Cases_on `c1` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_REWR_0],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_SUC,
                     bir_exec_step_state_def] >>
      Cases_on `(bir_exec_step prog s)` >>
      ASSUME_TAC (el 4 (CONJUNCTS bir_exec_step_n_REWRS)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_is_terminated_def, LET_DEF] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ]
  ]
]
);

val _ = export_theory();
