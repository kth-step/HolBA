open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open motorTheory;
open motor_specTheory;

val _ = new_theory "motor_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_motor_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

(* turn on the store-store cheater *)
val _ = birs_strategiesLib.birs_simp_select := birs_simp_instancesLib.birs_simp_default_riscv_gen true birs_simpLib.birs_simp_ID_fun [];

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_motor_prog_def
  motor_init_addr_def [motor_end_addr_def]
  bspec_motor_pre_def motor_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem motor_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
