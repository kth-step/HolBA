open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;
open balrob_miscTheory;
open balrob_faddTheory;
open balrob_fsubTheory;
open balrob_fmulTheory;
open balrob_fdivTheory;

val _ = new_theory "balrob_top";

(* ------------------------------------ *)


(*
val entry_name = "atan2f_own";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x10001438,
   [0x100014FA]);

val symb_exec_thm = birs_summary birs_prog_config
  [balrob_summary___lesf2_thm,
   balrob_summary_abs_own_thm,
   balrob_summary___aeabi_fadd_thm,
   balrob_summary___aeabi_fsub_thm,
   balrob_summary___aeabi_fmul_thm,
   balrob_summary___aeabi_fdiv_thm]
  reqs
  locs;
val balrob_summary_atan2f_own_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);
*)


(* ------------------------------------ *)


(*
val entry_name = "imu_handler_pid_entry";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x10001504,
   [0x100016e0]);

val symb_exec_thm = birs_summary birs_prog_config
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
*)


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();