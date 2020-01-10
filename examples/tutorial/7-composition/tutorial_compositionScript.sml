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
open bir_valuesTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;

open tutorial_compositionLib;

open bir_auxiliaryLib;

open HolBACoreSimps;
open HolBASimps;

val _ = new_theory "tutorial_composition";

(****************************************************************)
(* Step 1: *)
(* Translate HTs from bir_exec_to_labels_triple to bir_triple,
 * Then replace preconditions with shorthands and prove the
 * validity of this. *)
(* TODO: use_impl_rule uses cheats! *)

(* 28 -> 64 *)
val bir_add_reg_entry_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_entry_ht)
    contract_1_imp_taut_thm;
(* 32 -> 64 *)
(* TODO: This HT needs to have loop exit in its blacklist. Fix this in generation step. *)
val bir_add_reg_loop_variant_comp_ht =
(*use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_variant_ht)
    (Q.SPEC `v` contract_2v_imp_taut_thm)*)
  prove(
    ``bir_triple bir_add_reg_prog (BL_Address (Imm64 32w))
        (\x. (x = BL_Address (Imm64 64w)) \/ (x = BL_Address (Imm64 72w)))
        (bir_add_reg_contract_2_pre_variant v)
        (\l. if l = BL_Address (Imm64 64w)
             then (bir_add_reg_contract_2_post_variant v) (BL_Address (Imm64 64w))
             else bir_exp_false)``,
  cheat
);
(* 64 -> 32 *)
(* TODO: This HT needs to have loop exit in its blacklist. Fix this in generation step. *)
val bir_add_reg_loop_continue_variant_comp_ht =
(*use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_continue_variant_ht)
    (Q.SPEC `v` contract_3v_imp_taut_thm)*)
  prove(
    ``bir_triple bir_add_reg_prog (BL_Address (Imm64 64w))
        (\x. (x = BL_Address (Imm64 32w)) \/
             (x = BL_Address (Imm64 64w)) \/
             (x = BL_Address (Imm64 72w))
        )
        (bir_add_reg_contract_3_pre_variant v)
        (\l. if l = BL_Address (Imm64 32w)
             then (bir_add_reg_contract_3_post_variant v) (BL_Address (Imm64 32w))
             else bir_exp_false)``,
  cheat
);
(* 64 -> 72 *)
val bir_add_reg_loop_exit_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_exit_ht)
    contract_4_imp_taut_thm;

(****************************************************************)
(* Suggested new step 2: *)
(* Compose 64 -> 32 and 32 -> 64 sequentially (using bir_map_std_seq_comp_thm) *)

(* For debugging: *)
  val ht1 = bir_add_reg_loop_continue_variant_comp_ht; (* 64 -> 32 *)
  (* TODO: How to not assign whitelists and blacklists manually? EVAL with postcond and test for
   *       bir_exp_false? *)
  val whitelist1 = ``\l. l = BL_Address (Imm64 32w)``;
  val blacklist1 = ``\l. (l = BL_Address (Imm64 64w)) \/ (l = BL_Address (Imm64 72w))``;
  val ht2 = bir_add_reg_loop_variant_comp_ht; (* 32 -> 64 *)
  val whitelist2 = ``\l. l = BL_Address (Imm64 64w)``;
  val blacklist2 = ``\l. l = BL_Address (Imm64 72w)``;
  val invariant = bir_bool_expSyntax.bir_exp_true_tm
  (* The definitions of the program, plus any shorthands in postcondition of HT1
   * and precondition of HT2 *)
  (* TODO: Program definition could be bad to unfold in the wrong place, maybe that should be a
   * separate argument... *)
  val def_list = [bir_add_reg_prog_def, bir_add_reg_contract_3_post_variant_def,
		  bir_add_reg_contract_2_pre_variant_def];

(* TODO: Fix MP with ht1 in this procedure... *)
val loop_map_ht =
   bir_compose_seq ht1 whitelist1 blacklist1 ht2 whitelist2 blacklist2 invariant def_list;

(****************************************************************)
(* Suggested new step 3: *)
(* Compose loop from loop_map_ht and bir_add_reg_loop_exit_comp_ht (using bir_while_rule_thm) *)

(* TODO: Make new bir_compose_loop_new here, based on old bir_compose_loop. *)

(****************************************************************)
(* Suggested new step 4: *)
(* Compose loop intro with loop (using bir_map_std_seq_comp_thm) *)

(* TODO *)

(****************************************************************)
(*                             OLD                              *)
(****************************************************************)
(* Step 2: *)
(* Compose loop (using bir_while_rule_thm) *)

(* For debugging: *)
  val loop_ht = bir_add_reg_loop_variant_comp_ht;
  val loop_continuation_ht = bir_add_reg_loop_continue_variant_comp_ht;
  val loop_exit_ht = bir_add_reg_loop_exit_comp_ht;
  val loop_invariant = ``bir_add_reg_I``;
  val loop_condition = ``bir_add_reg_loop_condition``;
  val loop_variant = bden (bvar "R2" ``(BType_Imm Bit64)``);
  (* The definitions of the program, loop condition and precondition
   * of loop exit HT are used in a list for simplifications *)
  (* TODO: Program definition could be bad to unfold in the wrong place, maybe that should be a
   * separate argument... *)
  val def_list1 = [bir_add_reg_prog_def, bir_add_reg_loop_condition_def,
		  bir_add_reg_contract_4_pre_def];

val loop_to_end_ht =
  bir_compose_loop loop_ht loop_continuation_ht loop_exit_ht loop_invariant loop_condition
    loop_variant def_list1;

(****************************************************************)
(* Step 4: *)
(* Compose loop intro with loop (using bir_map_std_seq_comp_thm) *)

(* For debugging: *)
  val ht1 = bir_add_reg_entry_comp_ht;
  val ht2 = loop_to_end_ht;
  val def_list2 = [bir_add_reg_contract_1_post_def];

val final_ht_thm = bir_compose_seq ht1 ht2 def_list2;

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

(* TODO: Adjust the below to the new changes *)
(*
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
*)

val _ = export_theory();
