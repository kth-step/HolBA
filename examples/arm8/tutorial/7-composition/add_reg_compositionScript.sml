(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

open bir_prog_add_regTheory;
open tutorial_bir_to_armTheory add_reg_wpTheory
     add_reg_smtTheory;

open bir_wp_interfaceLib;

open bir_compositionLib;

open bslSyntax;

val _ = new_theory "add_reg_composition";

(****************************************************************)
(* Step 0: *)
(* Translate contracts from bir_exec_to_labels_triple to bir_simp_jgmt,
 * Then replace preconditions with shorthands and prove the
 * validity of this. *)

(* 28 -> 64 *)
val bir_add_reg_entry_comp_ct =
  bir_exec_to_labels_triple_to_bir_cont_predset bir_add_reg_entry_ht contract_1_imp_taut_thm;

(* 32 -> 64 *)
val bir_add_reg_loop_variant_comp_ct =
  bir_exec_to_labels_triple_to_bir_cont_predset bir_add_reg_loop_variant_ht contract_2v_imp_taut_thm;

(* 64 -> 32 *)
val bir_add_reg_loop_continue_variant_comp_ct =
  bir_exec_to_labels_triple_to_bir_cont_predset bir_add_reg_loop_continue_variant_ht contract_3v_imp_taut_thm;

(* 64 -> 72 *)
val bir_add_reg_loop_exit_comp_ct =
  bir_exec_to_labels_triple_to_bir_cont_predset bir_add_reg_loop_exit_ht contract_4_imp_taut_thm;

(****************************************************************)
(* Step 1: *)
(* Compose 64 -> 32 and 32 -> 64 sequentially (using bir_simp_std_seq_rule_thm) *)

(* For debugging:
  val bir_cont1 = bir_add_reg_loop_continue_variant_comp_ct; (* 64 -> 32 *)
  val bir_cont2 = bir_add_reg_loop_variant_comp_ct; (* 32 -> 64 *)
  (* The definitions of any shorthands in postcondition of contract 1
   * and precondition of contract 2 *)
  val def_list = [bir_add_reg_contract_3_post_variant_def,
		  bir_add_reg_contract_2_pre_variant_def];
*)

val loop_bir_cont =
  bir_compose_seq_predset bir_add_reg_loop_continue_variant_comp_ct bir_add_reg_loop_variant_comp_ct [bir_add_reg_contract_3_post_variant_def, bir_add_reg_contract_2_pre_variant_def];

(****************************************************************)
(* Step 2: *)
(* Ditch the loop re-entry label from the loop exit contract exclude list *)

(* For debugging:
  val to_remove_from_elist = ``{BL_Address (Imm64 32w)}``;
  val bir_cont = bir_add_reg_loop_exit_comp_ct;
*)

val loop_exit_bir_cont =
  bir_remove_labels_from_elist_predset bir_add_reg_loop_exit_comp_ct ``{BL_Address (Imm64 32w)}``;

(****************************************************************)
(* Step 3: *)
(* Compose loop from loop_bir_cont and loop_exit_bir_cont (using bir_while_rule_thm) *)

(* For debugging:
  val loop_bir_cont = loop_bir_cont;
  val loop_exit_bir_cont = loop_exit_bir_cont;
  val loop_invariant = ``bir_add_reg_I``;
  val loop_condition = ``bir_add_reg_loop_condition``;
  val loop_variant = bden (bvar "R2" ``(BType_Imm Bit64)``);
  val prog_def = ;
  (* The definitions of the loop condition and both preconditions *)
  val def_list = [bir_add_reg_loop_condition_def,
		  bir_add_reg_contract_3_pre_variant_def, bir_add_reg_contract_2_post_variant_def,
                  bir_add_reg_contract_4_pre_def];
*)

val loop_and_exit_ct =
  bir_compose_simp_loop_predset
    loop_bir_cont loop_exit_bir_cont ``bir_add_reg_I`` ``bir_add_reg_loop_condition`` (bden (bvar "R2" ``(BType_Imm Bit64)``)) bir_add_reg_prog_def [bir_add_reg_loop_condition_def,
		  bir_add_reg_contract_3_pre_variant_def, bir_add_reg_contract_2_post_variant_def,
                  bir_add_reg_contract_4_pre_def];

(****************************************************************)
(* Step 4: *)
(* Compose loop intro with loop (using bir_simp_std_seq_rule_thm) *)
(* For debugging:
  val bir_cont1 = bir_add_reg_entry_comp_ct
  val bir_cont2 = loop_and_exit_ct
  val def_list = [bir_add_reg_contract_1_post_def, bir_add_reg_I_def];
*)

val bir_add_reg_ct =
  bir_compose_seq_predset bir_add_reg_entry_comp_ct loop_and_exit_ct [bir_add_reg_contract_1_post_def, bir_add_reg_I_def];

val _ = save_thm("bir_add_reg_ct", bir_add_reg_ct);

val _ = export_theory();
