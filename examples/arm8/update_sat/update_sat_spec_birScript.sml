open HolKernel boolLib Parse bossLib;

open update_sat_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "update_sat_spec_bir";

(* ------------------------------------------------- *)
(* BSPEC contract, translated from the ARMv8 contract *)
(* ------------------------------------------------- *)

(* Defines bspec_update_sat_pre and bspec_update_sat_post *)

val (_, update_sat_arm8_pre_imp_bspec_pre) =
 arm8_pre_to_bir arm8_update_sat_pre_def;

val (_, update_sat_arm8_post_imp_bspec_post) =
 arm8_post_to_bir arm8_update_sat_post_def;

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem update_sat_arm8_pre_imp_bspec_pre_thm = update_sat_arm8_pre_imp_bspec_pre

Theorem update_sat_arm8_post_imp_bspec_post_thm = update_sat_arm8_post_imp_bspec_post

val _ = export_theory ();
