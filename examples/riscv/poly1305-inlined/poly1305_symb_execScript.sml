open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open poly1305Theory poly1305_specTheory;

val _ = new_theory "poly1305_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ------ *)
(* init *)
(* ------ *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_poly1305_prog_def
  poly1305_init_init_addr_def [poly1305_init_end_addr_def]
  bspec_poly1305_init_pre_def poly1305_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem poly1305_init_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
