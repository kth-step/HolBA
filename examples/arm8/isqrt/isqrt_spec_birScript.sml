open HolKernel boolLib Parse bossLib;

open isqrt_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "isqrt_spec_bir";

(* ------------------------------------------------- *)
(* BSPEC contracts, translated from ARMv8 conditions *)
(* ------------------------------------------------- *)

(* before loop contract *)

val (_, isqrt_arm8_pre_1_imp_bspec_pre_1) =
  arm8_pre_to_bir arm8_isqrt_pre_1_def;

val (_, isqrt_arm8_post_1_imp_bspec_post_1) =
  arm8_post_to_bir arm8_isqrt_post_1_def;

Theorem isqrt_arm8_pre_1_imp_bspec_pre_1_thm =
  isqrt_arm8_pre_1_imp_bspec_pre_1

Theorem isqrt_arm8_post_1_imp_bspec_post_1_thm =
  isqrt_arm8_post_1_imp_bspec_post_1

(* loop body contract *)

val (_, isqrt_arm8_pre_2_imp_bspec_pre_2) =
  arm8_pre_to_bir arm8_isqrt_pre_2_def;

val (_, isqrt_arm8_post_2_imp_bspec_post_2) =
  arm8_post_to_bir arm8_isqrt_post_2_def;

Theorem isqrt_arm8_pre_2_imp_bspec_pre_2_thm =
  isqrt_arm8_pre_2_imp_bspec_pre_2

Theorem isqrt_arm8_post_2_imp_bspec_post_2_thm =
  isqrt_arm8_post_2_imp_bspec_post_2

(* branch contract *)

val (_, isqrt_arm8_pre_3_imp_bspec_pre_3) =
  arm8_pre_to_bir arm8_isqrt_pre_3_def;

val (_, isqrt_arm8_post_3_imp_bspec_post_3) =
  arm8_post_cases_to_bir arm8_isqrt_post_3_def
    [arm8_isqrt_post_3_loop_def, arm8_isqrt_post_3_ret_def];

Theorem isqrt_arm8_pre_3_imp_bspec_pre_3_thm =
  isqrt_arm8_pre_3_imp_bspec_pre_3

Theorem isqrt_arm8_post_3_imp_bspec_post_3_thm =
  isqrt_arm8_post_3_imp_bspec_post_3

val _ = export_theory ();
