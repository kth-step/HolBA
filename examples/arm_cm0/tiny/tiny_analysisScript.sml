open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

val _ = new_theory "tiny_analysis";

val birs_prog_config = ((fst o dest_eq o concl) tinyLib.prog_def, tinyLib.birenvtyl_def);

val _ = set_default_cheat_setting ();

(* ------------------------------------ *)

val balrob_summary__reffunc_ld5_ldldbr8_thm =
  let
    val reqs = ((0, 0), 57);
    val locs =
      (0x08007110,
      [0x08007152]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
Theorem balrob_summary__reffunc_ld5_ldldbr8_thm =
  balrob_summary__reffunc_ld5_ldldbr8_thm;
val _ = print_result balrob_summary__reffunc_ld5_ldldbr8_thm ("0x8007152w", "bx lr", "3");


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
