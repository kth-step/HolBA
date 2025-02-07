open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open chachaTheory chacha_specTheory;

val _ = new_theory "chacha_symb_exec_ivsetup";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_chacha_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ------- *)
(* ivsetup *)
(* ------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_ivsetup_init_addr_def [chacha_ivsetup_end_addr_def]
  bspec_chacha_ivsetup_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_ivsetup_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
