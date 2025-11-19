open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fadd";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)

val fadd_offset = 0x1000030e - 0x257A + bin_offset1;

(* ------------------------------------ *)

val balrob_summary___aeabi_fadd_c1_thm =
  let
    val reqs = ((0, 0), 15);
    val locs =
      (fadd_offset + 0x257A,
      [fadd_offset + 0x2598]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fadd_c2_thm =
  let
    val reqs = ((0, 0), 29);
    val locs =
      (fadd_offset + 0x25A0,
      [fadd_offset + 0x24C2]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fadd_c3_thm =
  let
    val reqs = ((0, 0), 10);
    val locs =
      (fadd_offset + 0x25D0,
      [fadd_offset + 0x24C2]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)


val balrob_summary___aeabi_fadd_thm =
  let
    val reqs = ((0, 32), 168);
    val locs =
      ( 0x1000020c + bin_offset1,
      [0x10000268 + bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___clzsi2_thm,
       balrob_summary___aeabi_fadd_c1_thm,
       balrob_summary___aeabi_fadd_c2_thm,
       balrob_summary___aeabi_fadd_c3_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fadd_thm =
  balrob_summary___aeabi_fadd_thm;
val _ = print_result balrob_summary___aeabi_fadd_thm ("0x800447Cw", "pop {r3, r4, r5, r6, r7, pc}", "10");


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
