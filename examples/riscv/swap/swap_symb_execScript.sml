open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open swapTheory;
open swap_specTheory;

val _ = new_theory "swap_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_swap_prog_def
  swap_init_addr_def [swap_end_addr_def]
  bspec_swap_pre_def swap_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem swap_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
