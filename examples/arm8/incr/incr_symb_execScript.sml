open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open incrTheory;
open incr_spec_arm8Theory;
open incr_spec_birTheory;

val _ = new_theory "incr_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_incr_arm8_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_incr_prog_def
  incr_init_addr_def [incr_end_addr_def]
  bspec_incr_pre_def incr_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem incr_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
