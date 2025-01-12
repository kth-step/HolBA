open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;
open balrob_miscTheory;
open balrob_fadd_fakeTheory;
open balrob_fsub_fakeTheory;
open balrob_fmul_fakeTheory;
open balrob_fdiv_fakeTheory;
open balrob_ftopTheory;

val _ = new_theory "balrob_top";

val _ = birs_composeLib.compose_L_speedcheat := true;
val _ = balrob_supportLib.print_theorem_before_merging := true;

(* ------------------------------------ *)


val entry_name = "imu_handler_pid_entry";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x10001504,
   [0x100016e0]);

(*
val locs =
  ( 0x10001504,
   [0x1000151a]);
*)

val symb_exec_thm = birs_summary_gen
  (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x))
  (const_load_32_32_cheat_thms_fromprog_range (0x100016e4, 0x10001a88))
  birs_prog_config
  [balrob_summary_atan2f_own_thm,
   balrob_summary___lesf2_thm,
   balrob_summary___aeabi_i2f_thm,
   balrob_summary___aeabi_fadd_thm,
   balrob_summary___aeabi_fsub_thm,
   balrob_summary___aeabi_fmul_thm,
   balrob_summary___aeabi_fdiv_thm]
  reqs
  locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
