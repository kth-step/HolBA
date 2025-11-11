open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_misc";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

(* ------------------------------------ *)

val balrob_summary___aeabi_i2f_thm =
  let
    val reqs = ((0, 16), 89);
    val locs =
      (0x100012c8,
      [0x10001348]);
  in
    birs_summary birs_prog_config [balrob_summary___clzsi2_thm] reqs locs
  end;
Theorem balrob_summary___aeabi_i2f_thm =
  balrob_summary___aeabi_i2f_thm;

(* ------------------------------------ *)

(* cannot produce summary for __aeabi_fcmplt because enforcing merging to one state (not possible because of multiple exit points)
   this one will be inlined: in abs_own below and also in atan2f_own *)

(* ------------------------------------ *)

val balrob_summary_abs_own_thm =
  let
    val reqs = ((0, 36), 101);
    val locs =
      (0x1000140e,
      [0x10001434]);
  in
    birs_summary birs_prog_config [balrob_summary___lesf2_thm] reqs locs
  end;
Theorem balrob_summary_abs_own_thm =
  balrob_summary_abs_own_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
