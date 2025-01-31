open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open modexpTheory;
open modexp_specTheory;

val _ = new_theory "modexp_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_modexp_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_modexp_prog_def
  modexp_init_addr_def [modexp_end_addr_def]
  bspec_modexp_pre_def modexp_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem modexp_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
