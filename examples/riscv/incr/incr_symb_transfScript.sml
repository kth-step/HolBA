open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open incrTheory;
open incr_spec_riscvTheory;
open incr_spec_birTheory;
open incr_symb_execTheory;

val _ = new_theory "incr_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer_thm
  bir_incr_prog_def
  incr_init_addr_def incr_end_addr_def
  bspec_incr_pre_def bspec_incr_post_def
  incr_birenvtyl_def incr_prog_vars_list_def
  incr_symb_analysis_thm NONE incr_prog_vars_thm;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_thm);

Theorem bspec_cont_incr = bspec_cont_thm

val _ = export_theory ();
