open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fadd";

val fadd_offset = 0x1000030e - 0x257A;

(* ------------------------------------ *)

val entry_name = "__aeabi_fadd_c1";
val reqs = (0, 15);
val locs =
  ( fadd_offset + 0x257A,
   [fadd_offset + 0x2598]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fadd_c1_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fadd_c2";
val reqs = (0, 29);
val locs =
  ( fadd_offset + 0x25A0,
   [fadd_offset + 0x24C2]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fadd_c2_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fadd_c3";
val reqs = (0, 10);
val locs =
  ( fadd_offset + 0x25D0,
   [fadd_offset + 0x24C2]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fadd_c3_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

(*
val entry_name = "__aeabi_fadd";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x1000020c,
   [0x10000268]);

val symb_exec_thm = birs_summary birs_prog_config
  [balrob_summary___clzsi2_thm,
   balrob_summary___aeabi_fadd_c1_thm,
   balrob_summary___aeabi_fadd_c2_thm,
   balrob_summary___aeabi_fadd_c3_thm]
  reqs
  locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);
*)


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
