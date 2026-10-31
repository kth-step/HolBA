open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open add_regTheory; 
open add_reg_spec_arm8Theory;
open add_reg_spec_birTheory;

val _ = new_theory "add_reg_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_add_reg_arm8_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ------------------------- *)
(* before loop: jump to head *)
(* ------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_add_reg_prog_def
  add_reg_init_addr_1_def [add_reg_end_addr_1_def]
  bspec_add_reg_pre_1_def add_reg_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem add_reg_symb_analysis_1_thm = symb_analysis_thm

(* ----------- *)
(* loop branch *)
(* ----------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_add_reg_prog_def
  add_reg_init_addr_2_def [add_reg_end_addr_2_loop_def, add_reg_end_addr_2_ret_def]
  bspec_add_reg_pre_2_def add_reg_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem add_reg_symb_analysis_2_thm = symb_analysis_thm

(* --------- *)
(* loop body *)
(* --------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_add_reg_prog_def
  add_reg_init_addr_3_def [add_reg_end_addr_3_def]
  bspec_add_reg_pre_3_def add_reg_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem add_reg_symb_analysis_3_thm = symb_analysis_thm

val _ = export_theory ();
