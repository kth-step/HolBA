open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;
open balrob_miscTheory;
(*
open balrob_fadd_fakeTheory;
open balrob_fsub_fakeTheory;
open balrob_fmul_fakeTheory;
open balrob_fdiv_fakeTheory;
*)
open balrob_faddTheory;
open balrob_fsubTheory;
open balrob_fmulTheory;
open balrob_fdivTheory;

val _ = new_theory "balrob_ftop";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val bin_offset3 = 0x08006028 (*new*) - 0x10001438 (*old*); (* atan2f_own, imu_handler_pid_entry *)

(* ------------------------------------ *)


val balrob_summary_atan2f_own_thm =
  let
    val reqs = ((0, 92), 2038);
    val locs =
      (0x10001438+bin_offset3,
      [0x100014FA+bin_offset3]);
  in
    birs_summary birs_prog_config
      [balrob_summary___lesf2_thm,
       balrob_summary_abs_own_thm,
       balrob_summary___aeabi_fadd_thm,
       balrob_summary___aeabi_fsub_thm,
       balrob_summary___aeabi_fmul_thm,
       balrob_summary___aeabi_fdiv_thm]
      reqs
      locs
  end;
Theorem balrob_summary_atan2f_own_thm =
  balrob_summary_atan2f_own_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
