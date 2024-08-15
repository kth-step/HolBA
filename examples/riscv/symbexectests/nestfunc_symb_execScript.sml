open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open nestfuncTheory;
open nestfunc_specTheory;

val _ = new_theory "nestfunc_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_nestfunc_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_nestfunc_prog_def
  nestfunc_init_addr_def [nestfunc_end_addr_def]
  bspec_nestfunc_pre_def nestfunc_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem nestfunc_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
