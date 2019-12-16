open HolKernel Parse boolLib bossLib;
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;
open bslSyntax;
open tutorial_bir_to_armSupportTheory;
open tutorial_smtTheory;
open tutorial_compositionSupportTheory;
open examplesBinaryTheory;
open bir_wm_instTheory;
open bin_hoare_logicTheory;

open tutorial_compositionLib;

open bir_auxiliaryLib;

open HolBACoreSimps;

val _ = new_theory "tutorial_composition";

(* New workflow:

   1. Use bir_never_assumviol_block_n_ht_from_to_labels_ht to
      translate AV HT to non-AV HT (already done in tutorial_wpSupportLib.sml) - OK
   2. Use bir_label_ht_impl_weak_ht to translate bir_exec_to_labels_triple
      to bir_triple - OK
   3. Use the theorems in bir_wm_instTheory to compose:
      bir_invariant_rule_thm and bir_seq_rule_thm

*)

(* TODO for this to work:
 *
 *   Create translator from bir_triple to some bir_map_triple - theorem part OK, function TODO (need input format)
 *   Prove counterpart for BIR weakening rule (for bir_triple, and/or bir_map_triple?) - OK for both
 *   Prove counterpart for weak_map_std_seq_comp_thm - OK
 *   Change argument to WP prover and generator to real_end UNION next_end instead of real_end - TODO: Talk to Andreas if changes needed?
 *
 * *)

(* Step 1: *)
(* TODO: Assign new names to these after translating... *)
(* HTs translated from bir_exec_to_labels_triple to bir_triple: *)
val bir_add_reg_entry_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_entry_ht;
val bir_add_reg_loop_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_ht;
val bir_add_reg_loop_continue_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_continue_ht;
val bir_add_reg_loop_exit_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_exit_ht;
(* ... and variant HTs as well: *)
val bir_add_reg_loop_variant_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_variant_ht;
val bir_add_reg_loop_continue_variant_comp_ht =
  HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_continue_variant_ht;


(* Use the below line to debug use_impl_rule
 * (function can be found in tutorial_compositionLib):

  val (contract_thm, pre_impl_wp) = (bir_add_reg_entry_comp_ht, contract_1_imp_taut_thm);

*)
(* This will replace the preconditions in the HTs with the antecedents in the implications
 * supplied as second argument: basically, use_impl_rule applies the Hoare logic rule of consequence
 * for strengthening the precondition. *)
(* TODO: use_impl_rule uses cheats! *)
val bir_add_contract_1 = use_impl_rule bir_add_reg_entry_comp_ht contract_1_imp_taut_thm;
val bir_add_contract_2 = use_impl_rule bir_add_reg_loop_comp_ht contract_2_imp_taut_thm;
val bir_add_contract_3 = use_impl_rule bir_add_reg_loop_continue_comp_ht contract_3_imp_taut_thm;
val bir_add_contract_4 = use_impl_rule bir_add_reg_loop_exit_comp_ht contract_4_imp_taut_thm;

(* Same for contracts with loop variant: *)
val bir_add_contract_2v =
  use_impl_rule bir_add_reg_loop_variant_comp_ht (Q.SPEC `v` contract_2v_imp_taut_thm);
val bir_add_contract_3v =
  use_impl_rule bir_add_reg_loop_continue_variant_comp_ht (Q.SPEC `v` contract_3v_imp_taut_thm);

(* FIRST COMPOSITION: Loop composition *)
(* TODO: Compute variables of program once and store it... *)

(* Now, specialize the loop composition theorem (bir_invariant_rule_thm) in order to get
 * the already proved contracts as antecedents. *)
val bir_add_comp_invariant_rule_thm =
  ISPECL [get_contract_prog bir_add_contract_2v,
          get_contract_l bir_add_contract_2v,
          get_contract_ls bir_add_contract_2v,
          ``bir_add_reg_I``,
          ``bir_add_reg_loop_condition``,
          bden (bvar "R2" ``(BType_Imm Bit64)``),
          (* TODO: The below should be the postcondition we want with the new composition... *)
          ``\(x:bir_label_t). ^(get_contract_pre bir_add_contract_4)``] bir_invariant_rule_thm;

(* Attempt to prove the first antecedent of the specialised loop composition theorem and store the
 * result of modus ponens in thm1. *)
(* First antecedent is type_of_bir_exp of variant *)
val thm1 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) bir_add_comp_invariant_rule_thm)``,
                               (* TODO: Think about this... *)
                               SIMP_TAC (std_ss++holBACore_ss) []
                             )] bir_add_comp_invariant_rule_thm;

(* Second antecedent is set membership of variables in variant in variables of program *)
val thm2 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm1)``,
                               (* TODO: Use SUBSET proof
                                *       procedure here... *)
                               cheat
                             )] thm1;

(* Third antecedent is booleanity of loop condition *)
val thm3 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm2)``,
                               (* TODO: Use bir_is_bool_exp proof
                                *       procedure here... *)
                               cheat
                             )] thm2;

(* Fourth antecedent is set membership of variables in condition in variables of program *)
val thm4 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm3)``,
                               (* TODO: Use SUBSET proof
                                *       procedure here... *)
                               cheat
                             )] thm3;

(* Now, we use the two existing contracts (the special bir_loop_contract and loop exit): *)
(* bir_loop_contract signifies one loop iteration, with variant. loop exit contract should be
 * from start of loop with precondition that the condition does not hold. *)
(* TODO: These contracts do not, in fact, exist yet at this point... *)

(* Assuming we can fix these for now, we obtain the consequent: *)
val add_reg_loop_contract_thm =
  prove(``^((fst o dest_imp o snd o dest_imp o concl) thm4)``,

cheat
);


(* SECOND COMPOSITION: Sequential composition of loop + post-loop *)
(* Now, specialize the sequential composition theorem (bir_seq_rule_thm) in order to obtain the
 * BIR HT also including the execution after the loop. *)
val add_comp_seq_rule_thm =
  ISPECL [get_contract_prog add_reg_loop_contract_thm,
          get_contract_l add_reg_loop_contract_thm,
          get_contract_ls add_reg_loop_contract_thm,
          get_contract_ls bir_add_contract_4,
          get_contract_pre add_reg_loop_contract_thm, 
          ``\l. if l = BL_Address (Imm64 64w)
		then bir_add_reg_contract_4_pre
		else if l = BL_Address (Imm64 72w)
		then (bir_add_reg_post l)
		else bir_exp_false``] bir_seq_rule_thm;

(* Knock out first antecedent (contract for loop). *)
(* TODO: Should be obtained from add_reg_loop_contract_thm *)
(* OLD:
val thm1 =
  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) add_comp_seq_rule_thm)``,
                      ASSUME_TAC bir_add_contract_1 >>
                      UNDISCH_TAC (concl bir_add_contract_1) >>
                      computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                    )] add_comp_seq_rule_thm;
*)

(* OLD:
(* Knock out second antecedent (contract for post-loop) . *)
val add_reg_contract_thm =
  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm1)``,
                      ASSUME_TAC add_reg_loop_contract_thm >>
                      UNDISCH_TAC (concl add_reg_loop_contract_thm) >>
                      computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                    )] thm1;
*)

(* THIRD COMPOSITION: Sequential composition of pre-loop + (loop + post-loop) *)
val add_comp_seq_rule_thm2 =
  ISPECL [get_contract_prog add_reg_loop_contract_thm (* TODO *)] bir_seq_rule_thm;

(* Knock out first antecedent (contract for pre-loop). *)
(* TODO *)


(* Knock out second antecedent (contract for (loop + post-loop)). *)
(* TODO *)

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

(* Specialise lift_contract_thm in order to obtain the antecedents enabling translation from BIR to
 * ARM HT. *)
val add_lift_thm =
  ISPECL [get_contract_prog add_reg_contract_thm,
          ``bir_add_reg_progbin``,
          ``28w:word64``,
          ``{72w:word64}``,
          (((el 2) o snd o strip_comb o concl) examplesBinaryTheory.bir_add_reg_arm8_lift_THM),
          ``arm8_add_reg_pre``, ``arm8_add_reg_post``,
          get_contract_pre add_reg_contract_thm,
          get_contract_post add_reg_contract_thm] lift_contract_thm;

(* Prove the ARM triple by supplying the antecedents of lift_contract_thm *)
val arm_add_reg_contract_thm = prove(``^(concl (UNDISCH_ALL add_lift_thm))``,

ASSUME_TAC add_lift_thm >>
(* 1. Starting address exists in program *)
FULL_SIMP_TAC std_ss
  [EVAL ``MEM (^(get_contract_l add_reg_contract_thm))
              (bir_labels_of_program bir_add_reg_prog)``] >>
(* 2. Provide the BIR triple in the requisite format *)
ASSUME_TAC add_reg_contract_thm >>
SUBGOAL_THEN ``(\x. x = BL_Address (Imm64 72w)) = {BL_Address (Imm64 ml') | ml' IN {72w}}``
  (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >- (
  FULL_SIMP_TAC (srw_ss()) [GSYM pred_setTheory.IMAGE_DEF,
			    GSYM set_sepTheory.SEP_EQ_def,
			    stateTheory.SEP_EQ_SINGLETON]
) >>
(* 3. Provide the lifter theorem of the program *)
FULL_SIMP_TAC std_ss [examplesBinaryTheory.bir_add_reg_arm8_lift_THM] >>
(* 4. Prove that the union of variables in the program and precondition are a well-founded variable
 *    set *)
SUBGOAL_THEN
  ``arm8_wf_varset
      (bir_vars_of_program (^(get_contract_prog add_reg_contract_thm)) UNION
      bir_vars_of_exp bir_add_reg_pre)`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  (* TODO: We need to use a nice set-theoretical proof procedure to obtain the result that the
   * argument set is indeed the arm8_wf_varset *)
  (* TODO: Would subset also work here? *)
  cheat
) >>
(* 5. Provide translations of the ARM8 precondition to the BIR precondition, and of the ARM8
 *    postcondition to BIR postcondition *)
FULL_SIMP_TAC std_ss [arm8_pre_imp_bir_pre_thm, arm8_post_imp_bir_post_thm]
);


val _ = export_theory();
