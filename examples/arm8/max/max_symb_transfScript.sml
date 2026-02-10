open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open maxTheory;
open max_spec_arm8Theory;
open max_spec_birTheory;
open max_symb_execTheory;

val _ = new_theory "max_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer_thm
  bir_max_prog_def
  max_init_addr_def max_end_addr_def
  bspec_max_pre_def bspec_max_post_def
  max_birenvtyl_def max_prog_vars_list_def
  max_symb_analysis_thm NONE max_prog_vars_thm;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_thm);

Theorem bspec_cont_max = bspec_cont_thm

val _ = export_theory ();
