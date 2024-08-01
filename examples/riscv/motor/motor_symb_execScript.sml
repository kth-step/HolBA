open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open motorTheory;
open motor_specTheory;

val _ = new_theory "motor_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = birs_stepLib.patch_lifter_thm bir_motor_riscv_lift_THM;
val _ = birs_stepLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_motor_prog_def
  motor_init_addr_def [motor_end_addr_def]
  bspec_motor_pre_def motor_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem motor_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
