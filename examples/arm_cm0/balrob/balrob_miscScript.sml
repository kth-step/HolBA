open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_misc";


val entry_name = "__aeabi_i2f";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x100012c8,
   [0x10001348]);

val symb_exec_thm = birs_summary birs_prog_config [balrob_summary___clzsi2_thm] reqs locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)


(* TODO: cannot produce summary because enforcing merging to one state (not possible because of multiple exit points), did create_func_summary before not enforce this? maybe this was the reason why this summary was not usable?
   old comment: not usable at the moment, see abs_own *)
(*
val entry_name = "__aeabi_fcmplt";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x1000019c,
   [0x100001a8,
    0x100001ac]);

val symb_exec_thm = birs_summary birs_prog_config [balrob_summary___lesf2_thm] reqs locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);
*)


(* ------------------------------------ *)


val entry_name = "abs_own";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x1000140e,
   [0x10001434]);

val symb_exec_thm = birs_summary birs_prog_config [balrob_summary___lesf2_thm] reqs locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
