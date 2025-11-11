open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fsub";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val ffun_offset = 0x10000e7c - 0x2DEC (* fadd: 0xFFFDD94 *);

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c1_thm =
  let
    val reqs = ((0, 0), 13);
    val locs =
      (ffun_offset + 0x2DEC,
      [ffun_offset + 0x2DF4]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c2_thm =
  let
    val reqs = ((0, 0), 22);
    val locs =
      (ffun_offset + 0x2E60,
      [ffun_offset + 0x2E72]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c3_thm =
  let
    val reqs = ((0, 0), 11);
    val locs =
      (ffun_offset + 0x2EC6,
      [ffun_offset + 0x2EDC]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c4_thm =
  let
    val reqs = ((0, 0), 9);
    val locs =
      (ffun_offset + 0x3082,
      [ffun_offset + 0x3094]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c5_thm =
  let
    val reqs = ((0, 0), 11);
    val locs =
      (ffun_offset + 0x2F86,
      [ffun_offset + 0x2F9A]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c6_thm =
  let
    val reqs = ((0, 0), 6);
    val locs =
      (ffun_offset + 0x30CC,
      [ffun_offset + 0x30D8]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c7_thm =
  let
    val reqs = ((0, 0), 3);
    val locs =
      (ffun_offset + 0x2E5A,
      [ffun_offset + 0x2E5E]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c8_thm =
  let
    val reqs = ((0, 0), 16);
    val locs =
      (ffun_offset + 0x2E2C,
      [ffun_offset + 0x2E4A]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;


(* ------------------------------------ *)


val balrob_summary___aeabi_fsub_thm =
  let
    val reqs = ((0, 32), 187);
    val locs =
      ( 0x10000E50,
      [0x10000F14]);
  in
    birs_summary birs_prog_config
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
      locs
  end;
Theorem balrob_summary___aeabi_fsub_thm =
  balrob_summary___aeabi_fsub_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
