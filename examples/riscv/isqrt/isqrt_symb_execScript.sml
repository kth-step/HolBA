open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open isqrtTheory isqrt_specTheory;

val _ = new_theory "isqrt_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ----------- *)
(* before loop *)
(* ----------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_1_def [isqrt_end_addr_1_def]
  bspec_isqrt_pre_1_def isqrt_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_1_thm = symb_analysis_thm

(* --------- *)
(* loop body *)
(* --------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_2_def [isqrt_end_addr_2_def]
  bspec_isqrt_pre_2_def isqrt_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_2_thm = symb_analysis_thm

(* ----------- *)
(* loop branch *)
(* ----------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_3_def [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def]
  bspec_isqrt_pre_3_def isqrt_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_3_thm = symb_analysis_thm

val _ = export_theory ();
