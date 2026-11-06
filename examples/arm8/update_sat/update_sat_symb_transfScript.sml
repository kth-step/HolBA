open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open update_satTheory;
open update_sat_spec_arm8Theory;
open update_sat_spec_birTheory;
open update_sat_symb_execTheory;

val _ = new_theory "update_sat_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bir_cont_thm =
 bir_symb_transfer_thm
  bir_update_sat_prog_def
  update_sat_init_addr_def update_sat_end_addr_def
  arm8_update_sat_pre_bir_def arm8_update_sat_post_bir_def
  update_sat_birenvtyl_def update_sat_prog_vars_list_def
  update_sat_symb_analysis_thm NONE update_sat_prog_vars_thm;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bir_cont_thm);

Theorem bir_cont_update_sat = bir_cont_thm

val _ = export_theory ();
