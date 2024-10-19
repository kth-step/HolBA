open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open ifelseTheory ifelse_specTheory;

val _ = new_theory "ifelse_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_ifelse_prog_def
  ifelse_init_addr_def [ifelse_end_addr_def]
  bspec_ifelse_pre_def ifelse_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem ifelse_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
