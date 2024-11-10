open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;
open balrob_fsubTheory; (* TODO: remove this line later *)
open balrob_faddTheory; (* TODO: remove this line later *)
open balrob_fmulTheory; (* TODO: remove this line later *)

val _ = new_theory "balrob_fdiv";

val ffun_offset = 0x10000734 - 0x293C (* fadd: 0xFFFDD94 *);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_loop_body";
val reqs = (0, 9);
val locs =
  ( ffun_offset + 0x293C,
   [ffun_offset + 0x294E]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_loop_body_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_loop";
val reqs = (0, 381);
val locs =
  ( ffun_offset + 0x2930,
   [ffun_offset + 0x2952]);

val symb_exec_thm = birs_summary birs_prog_config [balrob_summary___aeabi_fdiv_loop_body_thm] reqs locs;
val balrob_summary___aeabi_fdiv_loop_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c1";
val reqs = (0, 15);
val locs =
  ( ffun_offset + 0x27CA,
   [ffun_offset + 0x27DC]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c1_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c3";
val reqs = (0, 7);
val locs =
  ( ffun_offset + 0x2842,
   [ffun_offset + 0x284E]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c3_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c4";
val reqs = (0, 6);
val locs =
  ( ffun_offset + 0x2850,
   [ffun_offset + 0x285A]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c4_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c5";
val reqs = (0, 7);
val locs =
  ( ffun_offset + 0x2996,
   [ffun_offset + 0x29A2]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c5_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c6";
val reqs = (0, 8);
val locs =
  ( ffun_offset + 0x29A4,
   [ffun_offset + 0x286A]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c6_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fdiv_c7";
val reqs = (0, 15);
val locs =
  ( ffun_offset + 0x2918,
   [ffun_offset + 0x286A]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fdiv_c7_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

(*
(* TODO: uses two jump table encoded in manually extracted cfg! *)
(* TODO: loads constants from memory! *)
val entry_name = "__aeabi_fdiv";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x100005A4,
   [0x10000678]);

val symb_exec_thm = birs_summary birs_prog_config
  [balrob_summary___clzsi2_thm,
   balrob_summary___aeabi_fdiv_loop_thm,
   balrob_summary___aeabi_fdiv_c1_thm,
   balrob_summary___aeabi_fdiv_c3_thm,
   balrob_summary___aeabi_fdiv_c4_thm,
   balrob_summary___aeabi_fdiv_c5_thm,
   balrob_summary___aeabi_fdiv_c6_thm,
   balrob_summary___aeabi_fdiv_c7_thm]
  reqs
  locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);
*)

(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
