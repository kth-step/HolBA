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

val _ = new_theory "tutorial_new_composition";

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
val bir_add_reg_loop_variant_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_variant_ht)
    (Q.SPEC `v` contract_2v_imp_taut_thm);
(* 64 -> 32 *)
val bir_add_reg_loop_continue_variant_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_continue_variant_ht)
    (Q.SPEC `v` contract_3v_imp_taut_thm);
(* 64 -> 72 *)
val bir_add_reg_loop_exit_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_exit_ht)
    contract_4_imp_taut_thm;

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
(* TODO: Make a function doing everything in step 4. *)

(* For debugging: *)
  val ht1 = bir_add_reg_entry_comp_ht;
  val ht2 = loop_to_end_ht;
  val def_list2 = [bir_add_reg_contract_1_post_def];

val final_ht_thm = bir_compose_seq ht1 ht2 def_list2;

val _ = export_theory();
