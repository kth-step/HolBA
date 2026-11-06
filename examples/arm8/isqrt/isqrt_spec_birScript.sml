open HolKernel boolLib Parse bossLib;

open isqrt_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "isqrt_spec_bir";

(* Each call translates an ARMv8 condition arm8_<c> to BIR: it defines
   bspec_<c> and saves the relation theorem arm8_<c>_to_bir_thm
   (see arm8_bir_condLib.sig) *)

(* before loop contract *)

val _ = arm8_pre_to_bir arm8_isqrt_pre_1_def;

val _ = arm8_post_to_bir arm8_isqrt_post_1_def;

(* loop body contract *)

val _ = arm8_pre_to_bir arm8_isqrt_pre_2_def;

val _ = arm8_post_to_bir arm8_isqrt_post_2_def;

(* loop branch contract *)

val _ = arm8_pre_to_bir arm8_isqrt_pre_3_def;

val _ = arm8_post_cases_to_bir arm8_isqrt_post_3_def
  [arm8_isqrt_post_3_loop_def, arm8_isqrt_post_3_ret_def];

val _ = export_theory ();
