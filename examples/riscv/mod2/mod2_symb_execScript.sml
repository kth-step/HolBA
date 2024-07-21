open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open mod2Theory mod2_specTheory;

val _ = new_theory "mod2_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_mod2_prog_def
  mod2_init_addr_def [mod2_end_addr_def]
  bspec_mod2_pre_def mod2_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem mod2_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem mod2_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
