open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;
(*
open balrob_fmulTheory; (* TODO: remove this line later *)
*)

val _ = new_theory "balrob_fsub";

val _ = birs_composeLib.compose_L_speedcheat := true;

val ffun_offset = 0x10000e7c - 0x2DEC (* fadd: 0xFFFDD94 *);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c1";
val reqs = (0, 13);
val locs =
  ( ffun_offset + 0x2DEC,
   [ffun_offset + 0x2DF4]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c1_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c2";
val reqs = (0, 22);
val locs =
  ( ffun_offset + 0x2E60,
   [ffun_offset + 0x2E72]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c2_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c3";
val reqs = (0, 11);
val locs =
  ( ffun_offset + 0x2EC6,
   [ffun_offset + 0x2EDC]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c3_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c4";
val reqs = (0, 9);
val locs =
  ( ffun_offset + 0x3082,
   [ffun_offset + 0x3094]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c4_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c5";
val reqs = (0, 11);
val locs =
  ( ffun_offset + 0x2F86,
   [ffun_offset + 0x2F9A]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c5_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c6";
val reqs = (0, 6);
val locs =
  ( ffun_offset + 0x30CC,
   [ffun_offset + 0x30D8]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c6_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c7";
val reqs = (0, 3);
val locs =
  ( ffun_offset + 0x2E5A,
   [ffun_offset + 0x2E5E]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c7_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fsub_c8";
val reqs = (0, 16);
val locs =
  ( ffun_offset + 0x2E2C,
   [ffun_offset + 0x2E4A]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fsub_c8_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)


val entry_name = "__aeabi_fsub";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x10000E50,
   [0x10000F14]);

val symb_exec_thm = birs_summary birs_prog_config
  [balrob_summary___clzsi2_thm,
   balrob_summary___aeabi_fsub_c1_thm,
   balrob_summary___aeabi_fsub_c2_thm,
   balrob_summary___aeabi_fsub_c3_thm,
   balrob_summary___aeabi_fsub_c4_thm,
   balrob_summary___aeabi_fsub_c5_thm,
   balrob_summary___aeabi_fsub_c6_thm,
   balrob_summary___aeabi_fsub_c7_thm,
   balrob_summary___aeabi_fsub_c8_thm]
  reqs
  locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
