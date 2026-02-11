open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open isqrtTheory;
open isqrt_spec_arm8Theory;
open isqrt_spec_birTheory;
open isqrt_symb_execTheory;

val _ = new_theory "isqrt_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val _ = show_tags := true;

(* before loop contract *)

val bspec_cont_1_thm =
 bir_symb_transfer_thm
  bir_isqrt_prog_def
  isqrt_init_addr_1_def isqrt_end_addr_1_def
  bspec_isqrt_pre_1_def bspec_isqrt_post_1_def
  isqrt_birenvtyl_def isqrt_prog_vars_list_def
  isqrt_symb_analysis_1_thm NONE isqrt_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_1_thm);

Theorem bspec_cont_isqrt_1 = bspec_cont_1_thm

(* loop body contract *)

val bspec_cont_2_thm =
 bir_symb_transfer_thm
  bir_isqrt_prog_def
  isqrt_init_addr_2_def isqrt_end_addr_2_def
  bspec_isqrt_pre_2_def bspec_isqrt_post_2_def
  isqrt_birenvtyl_def isqrt_prog_vars_list_def
  isqrt_symb_analysis_2_thm NONE isqrt_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_2_thm);

Theorem bspec_cont_isqrt_2 = bspec_cont_2_thm

(* branch contract *)

val bspec_cont_3_thm =
 bir_symb_transfer_two_thm
  bir_isqrt_prog_def
  isqrt_init_addr_3_def isqrt_end_addr_3_loop_def isqrt_end_addr_3_ret_def
  bspec_isqrt_pre_3_def bspec_isqrt_post_3_loop_def bspec_isqrt_post_3_ret_def
  isqrt_birenvtyl_def isqrt_prog_vars_list_def
  isqrt_symb_analysis_3_thm NONE isqrt_prog_vars_thm;

val _ = Portable.pprint Tag.pp_tag (tag bspec_cont_3_thm);

Theorem bspec_cont_isqrt_3 = bspec_cont_3_thm

val _ = export_theory ();
