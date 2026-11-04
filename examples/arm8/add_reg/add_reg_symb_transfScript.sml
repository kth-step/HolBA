open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open add_regTheory;
open add_reg_spec_arm8Theory;
open add_reg_spec_birTheory;
open add_reg_symb_execTheory;

val _ = new_theory "add_reg_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val _ = show_tags := true;

(* before loop contract, excluding the loop exit *)

val bspec_cont_1_thm =
 bir_symb_transfer_excl_thm
  bir_add_reg_prog_def
  add_reg_init_addr_1_def add_reg_end_addr_1_def add_reg_end_addr_def
  bspec_add_reg_pre_1_def bspec_add_reg_post_1_def
  add_reg_birenvtyl_def add_reg_prog_vars_list_def
  add_reg_symb_analysis_1_thm NONE add_reg_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_1_thm);

Theorem bspec_cont_add_reg_1 = bspec_cont_1_thm

(* branch contract *)

val bspec_cont_2_thm =
 bir_symb_transfer_two_thm
  bir_add_reg_prog_def
  add_reg_init_addr_2_def add_reg_end_addr_2_loop_def add_reg_end_addr_2_ret_def
  bspec_add_reg_pre_2_def bspec_add_reg_post_2_loop_def bspec_add_reg_post_2_ret_def
  add_reg_birenvtyl_def add_reg_prog_vars_list_def
  add_reg_symb_analysis_2_thm NONE add_reg_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_2_thm);

Theorem bspec_cont_add_reg_2 = bspec_cont_2_thm

(* loop body contract, excluding the loop exit *)

val bspec_cont_3_thm =
 bir_symb_transfer_excl_thm
  bir_add_reg_prog_def
  add_reg_init_addr_3_def add_reg_end_addr_3_def add_reg_end_addr_def
  bspec_add_reg_pre_3_def bspec_add_reg_post_3_def
  add_reg_birenvtyl_def add_reg_prog_vars_list_def
  add_reg_symb_analysis_3_thm NONE add_reg_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_3_thm);

Theorem bspec_cont_add_reg_3 = bspec_cont_3_thm

val _ = export_theory ();
