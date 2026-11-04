open HolKernel boolLib Parse bossLib;

open swap_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "swap_spec_bir";

(* ------------------------------------------------- *)
(* BSPEC contract, translated from the ARMv8 contract *)
(* ------------------------------------------------- *)

(* Defines bspec_swap_pre and bspec_swap_post *)

val (_, swap_arm8_pre_imp_bspec_pre) = arm8_pre_to_bir arm8_swap_pre_def;

val (_, swap_arm8_post_imp_bspec_post) = arm8_post_to_bir arm8_swap_post_def;

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem swap_arm8_pre_imp_bspec_pre_thm = swap_arm8_pre_imp_bspec_pre

Theorem swap_arm8_post_imp_bspec_post_thm = swap_arm8_post_imp_bspec_post

val _ = export_theory ();
