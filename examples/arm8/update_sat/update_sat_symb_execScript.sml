open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open update_satTheory;
open update_sat_spec_arm8Theory;
open update_sat_spec_birTheory;

val _ = new_theory "update_sat_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_update_sat_arm8_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_update_sat_prog_def
  update_sat_init_addr_def [update_sat_end_addr_def]
  arm8_update_sat_pre_bir_def update_sat_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem update_sat_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
