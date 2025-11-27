open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;

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
open balrob_ftopTheory;

val _ = new_theory "balrob_top";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();
(*val _ = birs_armcm0_supportLib.print_theorem_before_merging := true;*)

val bin_offset4 = 0x08006218 (*new*) - 0x10001504 (*old*); (* imu_handler_pid_entry *)

(* ------------------------------------ *)

val _ = birs_instantiationLib.set_renamesymb_counter 2000;

val gen_arg1 = (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x));
val gen_arg2 = (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x080063f8, 0x08006444));

val summary_thms = (*__aeabi_fcmplt*)
  [balrob_summary_atan2f_own_thm,
   balrob_summary___lesf2_thm,
   balrob_summary___aeabi_i2f_thm,
   balrob_summary___aeabi_fadd_thm,
   balrob_summary___aeabi_fsub_thm,
   balrob_summary___aeabi_fmul_thm,
   balrob_summary___aeabi_fdiv_thm];

val balrob_summary_imu_handler_pid_entry_c1_thm =
  let
    val reqs = ((0, 204), 2577);
    val locs =
      (0x10001504+bin_offset4 (*0x1000153c*),
      [0x10001576+bin_offset4]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      summary_thms
      reqs
      locs
  end;
(*val _ = print "balrob_summary_imu_handler_pid_entry_c1_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary_imu_handler_pid_entry_c1_thm;*)

val balrob_summary_imu_handler_pid_entry_c2_thm =
  let
    val reqs = ((0, 204), 5474);
    val locs =
      (0x10001504+bin_offset4 (*0x1000164E*),
      [0x1000166E+bin_offset4]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      ([balrob_summary_imu_handler_pid_entry_c1_thm]@summary_thms)
      reqs
      locs
  end;
(*val _ = print "balrob_summary_imu_handler_pid_entry_c2_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary_imu_handler_pid_entry_c2_thm;*)


val balrob_summary_imu_handler_pid_entry_thm =
  let
    val reqs = ((0, 204), 7522);
    val locs =
      (0x10001504+bin_offset4,
      [0x100016e0+bin_offset4]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      ([balrob_summary_imu_handler_pid_entry_c2_thm]@summary_thms)
      reqs
      locs
  end;
Theorem balrob_summary_imu_handler_pid_entry_thm =
  balrob_summary_imu_handler_pid_entry_thm;
val _ = print_result balrob_summary_imu_handler_pid_entry_thm ("0x80063F4w", "pop {r4, r7, pc}", "7");


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
