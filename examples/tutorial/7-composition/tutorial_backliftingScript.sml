open HolKernel Parse boolLib bossLib;

open examplesBinaryTheory tutorial_bir_to_armTheory
     tutorial_bir_to_armSupportTheory tutorial_compositionTheory;
open bir_wm_instTheory;

open tutorial_compositionLib;
open bir_auxiliaryLib;

val _ = new_theory "tutorial_backlifting";

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

(* Specialise lift_contract_thm in order to obtain the antecedents enabling translation from BIR to
 * ARM HT. *)
val add_lift_thm =
  ISPECL [get_bir_map_triple_prog bir_add_reg_ct,
          ``bir_add_reg_progbin``,
          ``28w:word64``,
          ``{72w:word64}``,
          (((el 2) o snd o strip_comb o concl) examplesBinaryTheory.bir_add_reg_arm8_lift_THM),
          ``arm8_add_reg_pre``, ``arm8_add_reg_post``,
          get_bir_map_triple_pre bir_add_reg_ct,
          get_bir_map_triple_post bir_add_reg_ct] tutorial_bir_to_armSupportTheory.lift_contract_thm;

(* Prove the ARM triple by supplying the antecedents of lift_contract_thm *)
val arm_add_reg_contract_thm = store_thm("arm_add_reg_contract_thm",
  ``arm8_triple bir_add_reg_progbin 28w {72w} arm8_add_reg_pre
            arm8_add_reg_post``,

irule add_lift_thm >>
REPEAT STRIP_TAC >| [
  (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
   *    set *)
  (* TODO: This subset computation is slooow... *)
  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++HolBASimps.VARS_OF_PROG_ss
                       ++pred_setLib.PRED_SET_ss)
    [bir_add_reg_prog_def, bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def, arm8_wf_varset_def,
     arm8_vars_def],

  (* 2. Starting address exists in program *)
  FULL_SIMP_TAC std_ss
    [EVAL ``MEM (^(get_bir_map_triple_start_label bir_add_reg_ct))
		(bir_labels_of_program bir_add_reg_prog)``],

  (* 3. Provide translation of the ARM8 precondition to the BIR precondition *)
  FULL_SIMP_TAC std_ss [bir_add_reg_contract_1_pre_def, arm8_pre_imp_bir_pre_thm],

  (* 4. Provide translation of the ARM8 postcondition to BIR postcondition *)
  FULL_SIMP_TAC std_ss [bir_add_reg_contract_4_post_def] >>
  ASSUME_TAC (Q.SPEC `{BL_Address (Imm64 ml') | ml' IN {72w}}` arm8_post_imp_bir_post_thm) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_arm8_def] >>
  FULL_SIMP_TAC std_ss [],

  (* 5. Provide the lifter theorem of the program *)
  FULL_SIMP_TAC std_ss [examplesBinaryTheory.bir_add_reg_arm8_lift_THM],

  (* 6. Provide the BIR triple in the requisite format *)
  ASSUME_TAC (CONJUNCT2 (SIMP_RULE std_ss [bir_triple_equiv_map_triple] bir_add_reg_ct)) >>
  FULL_SIMP_TAC std_ss [pred_setTheory.UNION_EMPTY] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>

  (*      Precondition: *)
  FULL_SIMP_TAC std_ss [bir_triple_def, bin_hoare_logicTheory.weak_triple_def,
			bir_exec_to_labels_triple_precond_def,
			bir_exec_to_labels_triple_postcond_def, bir_exp_equivTheory.bir_and_op2,
			bir_bool_expTheory.bir_is_bool_exp_env_REWRS] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  Cases_on `s'.bst_pc.bpc_label = BL_Address (Imm64 72w)` >> (
    FULL_SIMP_TAC std_ss [bir_exp_equivTheory.bir_and_op2,
                          bir_bool_expTheory.bir_is_bool_exp_env_REWRS]
  ) >>
  FULL_SIMP_TAC (std_ss++bin_hoare_logicSimps.bir_wm_SS)
    [bir_etl_wm_def, bir_weak_trs_def,
     bir_programTheory.bir_exec_to_labels_def,
     bir_programTheory.bir_exec_to_labels_n_def] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
]
);

val _ = export_theory();
