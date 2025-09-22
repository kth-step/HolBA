open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aes_unoptTheory aes_unopt_specTheory;

val _ = new_theory "aes_unopt_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_aes_unopt_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_aes_unopt_prog_def
  aes_init_addr_def [aes_end_addr_def]
  bspec_aes_pre_def aes_unopt_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem aes_unopt_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
