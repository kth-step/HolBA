open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_misc";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val bin_offset0 = 0x08004000 (*new*) - 0x10000000 (*old*); (* __udivsi3, __aeabi_uidivmod *)
val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)
val bin_offset2 = 0x08006000 (*new*) - 0x1000140e (*old*); (* abs_own *)
val bin_offset3 = 0x08006028 (*new*) - 0x10001438 (*old*); (* atan2f_own *)

(* ------------------------------------ *)

val balrob_summary___aeabi_i2f_thm =
  let
    val reqs = ((0, 16), 89);
    val locs =
      (0x100012c8+bin_offset1,
      [0x10001348+bin_offset1]);
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
      (0x1000140e+bin_offset2,
      [0x10001434+bin_offset2]);
  in
    birs_summary birs_prog_config [balrob_summary___lesf2_thm] reqs locs
  end;
Theorem balrob_summary_abs_own_thm =
  balrob_summary_abs_own_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
