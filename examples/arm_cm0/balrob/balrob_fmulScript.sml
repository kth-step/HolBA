open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fmul";

val ffun_offset = 0x10000c28 - 0x2C40 (* fadd: 0xFFFDD94 *);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c1";
val reqs = (0, 11);
val locs =
  ( ffun_offset + 0x2C40,
   [ffun_offset + 0x2BB2]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c1_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c2";
val reqs = (0, 5);
val locs =
  ( ffun_offset + 0x2C7C,
   [ffun_offset + 0x2C86]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c2_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c4";
val reqs = (0, 7);
val locs =
  ( ffun_offset + 0x2CB8,
   [ffun_offset + 0x2CC4]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c4_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c5";
val reqs = (0, 7);
val locs =
  ( ffun_offset + 0x2CC6,
   [ffun_offset + 0x2CD0]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c5_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c6";
val reqs = (0, 16);
val locs =
  ( ffun_offset + 0x2D40,
   [ffun_offset + 0x2C12]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c6_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c7";
val reqs = (0, 8);
val locs =
  ( ffun_offset + 0x2CD2,
   [ffun_offset + 0x2C12]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c7_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

(* ------------------------------------ *)

val entry_name = "__aeabi_fmul_c8";
val reqs = (0, 16);
val locs =
  ( ffun_offset + 0x2D70,
   [ffun_offset + 0x2C12]);

val symb_exec_thm = birs_summary birs_prog_config [] reqs locs;
val balrob_summary___aeabi_fmul_c8_thm = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);


(* ------------------------------------ *)

(*
(* TODO: uses one jump table encoded in manually extracted cfg! takes 3 times as much time as sub or div *)
val entry_name = "__aeabi_fmul";
val reqs = get_fun_usage entry_name;
val locs =
  ( 0x10000B44,
   [0x10000C12]);

val symb_exec_thm = birs_summary birs_prog_config
  [balrob_summary___clzsi2_thm,
   balrob_summary___aeabi_fmul_c1_thm,
   balrob_summary___aeabi_fmul_c2_thm,
   balrob_summary___aeabi_fmul_c4_thm,
   balrob_summary___aeabi_fmul_c5_thm,
   balrob_summary___aeabi_fmul_c6_thm,
   balrob_summary___aeabi_fmul_c7_thm,
   balrob_summary___aeabi_fmul_c8_thm]
  reqs
  locs;
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);
*)


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
