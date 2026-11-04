open HolKernel boolLib Parse bossLib;

open max_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "max_spec_bir";

(* ------------------------------------------------- *)
(* BSPEC contract, translated from the ARMv8 contract *)
(* ------------------------------------------------- *)

(* Defines bspec_max_pre and bspec_max_post *)

val (_, max_arm8_pre_imp_bspec_pre) = arm8_pre_to_bir arm8_max_pre_def;

val (_, max_arm8_post_imp_bspec_post) = arm8_post_to_bir arm8_max_post_def;

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem max_arm8_pre_imp_bspec_pre_thm = max_arm8_pre_imp_bspec_pre

Theorem max_arm8_post_imp_bspec_post_thm = max_arm8_post_imp_bspec_post

val _ = export_theory ();
