open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;
open birs_armcm0_concretizationLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fdiv";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();
val _ = birs_basic_execute_concretization_resolver := SOME (concretization_resolver ((rhs o concl) balrobTheory.bir_balrob_progbin_def));

val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)

val ffun_offset = 0x10000734 - 0x293C (* fadd: 0xFFFDD94 *) + bin_offset1;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_loop_thm =
  let
    val balrob_summary___aeabi_fdiv_loop_body_thm =
      let
        val reqs = ((0, 0), 9);
        val locs =
          (ffun_offset + 0x293C,
          [ffun_offset + 0x294E]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 381);
    val locs =
      (ffun_offset + 0x2930,
      [ffun_offset + 0x2952]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fdiv_loop_body_thm] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c1_thm =
  let
    val reqs = ((0, 0), 15);
    val locs =
      (ffun_offset + 0x27CA,
      [ffun_offset + 0x27DC]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c3_thm =
  let
    val reqs = ((0, 0), 7);
    val locs =
      (ffun_offset + 0x2842,
      [ffun_offset + 0x284E]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c4_thm =
  let
    val reqs = ((0, 0), 6);
    val locs =
      (ffun_offset + 0x2850,
      [ffun_offset + 0x285A]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c5_thm =
  let
    val reqs = ((0, 0), 7);
    val locs =
      (ffun_offset + 0x2996,
      [ffun_offset + 0x29A2]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c6_thm =
  let
    val reqs = ((0, 0), 8);
    val locs =
      (ffun_offset + 0x29A4,
      [ffun_offset + 0x286A]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c7_thm =
  let
    val reqs = ((0, 0), 15);
    val locs =
      (ffun_offset + 0x2918,
      [ffun_offset + 0x286A]);
  in
    birs_summary birs_prog_config [] reqs locs
  end

(* ------------------------------------ *)


(* TODO: uses two jump table encoded in manually extracted cfg! *)
(* TODO: loads constants from memory! *)
val balrob_summary___aeabi_fdiv_thm =
  let
    val reqs = ((0, 40), 581);
    val locs =
      (0x100005A4 + bin_offset1,
      [0x10000678 + bin_offset1]);
  in
    birs_summary_gen
      (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x))
      ((const_load_32_32_cheat_thms_fromprog ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x100007bc+bin_offset1, 1))@
       (const_load_32_32_cheat_thms_fromprog ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x100007c4+bin_offset1, 1)))
      birs_prog_config
      [balrob_summary___clzsi2_thm,
       balrob_summary___aeabi_fdiv_loop_thm,
       balrob_summary___aeabi_fdiv_c1_thm,
       balrob_summary___aeabi_fdiv_c3_thm,
       balrob_summary___aeabi_fdiv_c4_thm,
       balrob_summary___aeabi_fdiv_c5_thm,
       balrob_summary___aeabi_fdiv_c6_thm,
       balrob_summary___aeabi_fdiv_c7_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fdiv_thm =
  balrob_summary___aeabi_fdiv_thm;
val _ = print_result balrob_summary___aeabi_fdiv_thm ("0x800488Cw", "pop {r3, r4, r5, r6, r7, pc}", "10");


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
