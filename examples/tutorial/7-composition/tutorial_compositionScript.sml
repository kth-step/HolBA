open HolKernel Parse boolLib bossLib;
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;
open bslSyntax;
open tutorial_bir_to_armSupportTheory;
open tutorial_smtTheory;
open tutorial_compositionLib;
open tutorial_compositionSupportTheory;
open examplesBinaryTheory;

val _ = new_theory "tutorial_composition";

(* Use the below line to debug use_impl_rule (from tutorial_compositionLib):

  val (contract_thm, pre_impl_wp) = (bir_add_reg_entry_ht, contract_1_imp_taut_thm);

*)
(* This will replace the preconditions in the HTs with the antecedents in the implications
 * supplied as second argument: basically, use_impl_rule applies the Hoare logic rule of consequence
 * for strengthening the precondition. *)
val bir_add_contract_1 = use_impl_rule bir_add_reg_entry_ht contract_1_imp_taut_thm;
val bir_add_contract_2 = use_impl_rule bir_add_reg_loop_ht contract_2_imp_taut_thm;
val bir_add_contract_3 = use_impl_rule bir_add_reg_loop_continue_ht contract_3_imp_taut_thm;
val bir_add_contract_4 = use_impl_rule bir_add_reg_loop_exit_ht contract_4_imp_taut_thm;

(* Same for contracts with loop variant: *)
val bir_add_contract_2v =
  use_impl_rule bir_add_reg_loop_variant_ht (Q.SPEC `v` contract_2v_imp_taut_thm);
val bir_add_contract_3v =
  use_impl_rule bir_add_reg_loop_continue_variant_ht (Q.SPEC `v` contract_3v_imp_taut_thm);


(* Now, specialize the loop composition theorem (comp_loop_thm) in order to obtain the already proved
 * contracts as antecedents. *)
val add_comp_loop_rule_thm =
  ISPECL [get_contract_l bir_add_contract_3v,
          get_contract_l bir_add_contract_2v,
          get_contract_ls bir_add_contract_4,
          get_contract_prog bir_add_contract_3,
          ``bir_add_reg_I``,
          ``bir_add_reg_loop_condition``,
          get_contract_post bir_add_contract_4,
          bden (bvar "R2" ``(BType_Imm Bit64)``),
          ``v:word64``] comp_loop_thm;

(* Attempt to prove the first antecedent of the specialised loop composition theorem and store the
 * result of modus ponens in thm1. *)
val thm1 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) add_comp_loop_rule_thm)``,
                               ASSUME_TAC bir_add_contract_2v >>
                               UNDISCH_TAC (concl bir_add_contract_2v) >>
                               computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                             )] add_comp_loop_rule_thm;

(* Do the same thing for the second antecedent. *)
(* TODO: Why do we need to use RESTR_EVAL_TAC twice here? *)
val thm2 = SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm1)``,
                               ASSUME_TAC bir_add_contract_3v >>
                               UNDISCH_TAC (concl bir_add_contract_3v) >>
                               (NTAC 2 (computeLib.RESTR_EVAL_TAC
                                  [``bir_triple``, ``bir_add_reg_prog``]))
                             )] thm1;

(* Do the same thing for the third antecedent, obtaining the conclusion. *)
val add_reg_loop_contract_thm =
  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm2)``,
                      ASSUME_TAC bir_add_contract_4 >>
                      UNDISCH_TAC (concl bir_add_contract_4) >>
                      computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                    )] thm2;


(* Now, specialize the sequential composition theorem (comp_seq_thm) in order to obtain the
 * final complete BIR HT, also including the prelude to the loop. *)
val add_comp_seq_rule_thm =
  ISPECL [get_contract_l bir_add_contract_1,
          get_contract_l add_reg_loop_contract_thm,
          get_contract_ls add_reg_loop_contract_thm,
          get_contract_prog add_reg_loop_contract_thm,
          ``bir_add_reg_pre``,
          ``\(l:bir_label_t). ^(get_contract_pre add_reg_loop_contract_thm)``,
          ``\(l:bir_label_t). bir_add_reg_post``] comp_seq_thm;

(* Knock out first antecedent (contract for preamble of loop). *)
val thm1 =
  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) add_comp_seq_rule_thm)``,
                      ASSUME_TAC bir_add_contract_1 >>
                      UNDISCH_TAC (concl bir_add_contract_1) >>
                      computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                    )] add_comp_seq_rule_thm;

(* Knock out second antecedent (contract for preamble of loop), obtaining the HT for the entire
 * program. *)
val add_reg_contract_thm =
  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) thm1)``,
                      ASSUME_TAC add_reg_loop_contract_thm >>
                      UNDISCH_TAC (concl add_reg_loop_contract_thm) >>
                      computeLib.RESTR_EVAL_TAC [``bir_triple``, ``bir_add_reg_prog``]
                    )] thm1;


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
