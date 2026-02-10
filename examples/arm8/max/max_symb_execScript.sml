open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open maxTheory;
open max_spec_arm8Theory;
open max_spec_birTheory;

val _ = new_theory "max_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_max_arm8_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_max_prog_def
  max_init_addr_def [max_end_addr_def]
  bspec_max_pre_def max_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem max_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
