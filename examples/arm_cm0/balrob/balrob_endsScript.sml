open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

val _ = new_theory "balrob_ends";

val entry_name = "__clzsi2";
val reqs = get_fun_usage entry_name;
val locs =
  (0x100013b4,
   0x100013dc);

val symb_exec_thm = birs_summary birs_prog_config reqs locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)
(*
val entry_name = "__lesf2";
val reqs = get_fun_usage entry_name;
val locs =
  (0x10000a4c,
   0x10000ad2);

val symb_exec_thm = birs_summary birs_prog_config reqs locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)
*)

val _ = export_theory ();
