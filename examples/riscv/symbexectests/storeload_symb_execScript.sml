open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open storeloadTheory;
open storeload_specTheory;

val _ = new_theory "storeload_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = bir_storeload_riscv_lift_THM;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_storeload_prog_def
  storeload_init_addr_def [storeload_end_addr_def]
  bspec_storeload_pre_def storeload_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem storeload_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
