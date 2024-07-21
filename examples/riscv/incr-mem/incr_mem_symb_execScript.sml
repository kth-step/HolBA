open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open incr_memTheory;
open incr_mem_specTheory;

val _ = new_theory "incr_mem_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_incr_mem_prog_def
  incr_mem_init_addr_def [incr_mem_end_addr_def]
  bspec_incr_mem_pre_def incr_mem_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem incr_mem_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem incr_mem_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
