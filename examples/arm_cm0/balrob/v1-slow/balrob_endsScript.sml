open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

val _ = new_theory "balrob_ends";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

(* ------------------------------------ *)

val balrob_summary___clzsi2_thm =
  let
    val reqs = ((0, 0), 21);
    val locs =
      (0x100013b4,
      [0x100013dc]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
Theorem balrob_summary___clzsi2_thm =
  balrob_summary___clzsi2_thm;

(* ------------------------------------ *)

val balrob_summary___lesf2_thm =
  let
    val reqs = ((0, 12), 49);
    val locs =
      (0x10000a4c,
      [0x10000ad2]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
Theorem balrob_summary___lesf2_thm =
  balrob_summary___lesf2_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
