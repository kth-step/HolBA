open HolKernel boolLib Parse bossLib;

open update_sat_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "update_sat_spec_bir";

(* Each call translates an ARMv8 condition arm8_<c> to BIR: it defines
   bspec_<c> and saves the relation theorem arm8_<c>_to_bir_thm
   (see arm8_bir_condLib.sig) *)

val _ = arm8_pre_to_bir arm8_update_sat_pre_def;

val _ = arm8_post_to_bir arm8_update_sat_post_def;

val _ = export_theory ();
