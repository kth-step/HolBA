open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;
open birs_armcm0_concretizationLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fmul";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();
val _ = birs_basic_execute_concretization_resolver := SOME (concretization_resolver ((rhs o concl) balrobTheory.bir_balrob_progbin_def));

val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)

val ffun_offset = 0x10000c28 - 0x2C40 (* fadd: 0xFFFDD94 *)+bin_offset1;
(*FFFDFE8*)

(* ------------------------------------ *)

(* --------------------======================== TOP PART START ========================---------------- *)

val balrob_summary___aeabi_fmul_c1_thm =
  let
    val reqs = ((0, 0), 11);
    val locs =
      (ffun_offset + 0x2C40,
      [ffun_offset + 0x2BB2]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

val balrob_summary___aeabi_fmul_part_top_thm =
  let
    val reqs = ((0, 44), 124);
    val locs =
      (0x10000B44+bin_offset1,(*ffun_offset + 0x2B7A,*)
      [ffun_offset + 0x2BB2]);
  in
    birs_summary
      birs_prog_config
      [balrob_summary___clzsi2_thm,
      balrob_summary___aeabi_fmul_c1_thm] reqs locs
  end;

(* --------------------======================== TOP PART END ========================---------------- *)

(* --------------------======================== BOT PART START ========================---------------- *)

val balrob_summary___aeabi_fmul_c2brace_thm =
  let
    val balrob_summary___aeabi_fmul_c2_thm =
      let
        val reqs = ((0, 0), 5);
        val locs =
          (ffun_offset + 0x2C7C,
          [ffun_offset + 0x2C86]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((~48, 44), 48);
    val locs =
      (ffun_offset + 0x2C54,(*(*inner one starts at: *)0x2CA4,*)
      [ffun_offset + 0x2CAE]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fmul_c2_thm] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fmul_c6_thm =
  let
    val reqs = ((0, 0), 16);
    val locs =
      (ffun_offset + 0x2D40,
      [ffun_offset + 0x2C12]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fmul_c4578_thm =
  let
    val balrob_summary___aeabi_fmul_c4_thm =
      let
        val reqs = ((0, 0), 7);
        val locs =
          (ffun_offset + 0x2CB8,
          [ffun_offset + 0x2CC4]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val balrob_summary___aeabi_fmul_c5_thm =
      let
        val reqs = ((0, 0), 7);
        val locs =
          (ffun_offset + 0x2CC6,
          [ffun_offset + 0x2CD0]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val balrob_summary___aeabi_fmul_c7_thm =
      let
        val reqs = ((0, 0), 8);
        val locs =
          (ffun_offset + 0x2CD2,
          [ffun_offset + 0x2C12]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val balrob_summary___aeabi_fmul_c8_thm =
      let
        val reqs = ((0, 0), 16);
        val locs =
          (ffun_offset + 0x2D70,
          [ffun_offset + 0x2C12]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 35);
    val locs =
      (ffun_offset + 0x2CB4,
      [ffun_offset + 0x2C12]);

  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fmul_c4_thm,
      balrob_summary___aeabi_fmul_c5_thm,
      balrob_summary___aeabi_fmul_c7_thm,
      balrob_summary___aeabi_fmul_c8_thm] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fmul_c4578brace_thm =
  let
    val reqs = ((0, 0), 50);
    val locs =
      (ffun_offset + 0x2C02,
      [ffun_offset + 0x2C12]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fmul_c4578_thm] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fmul_part_bot_thm =
  let
    val reqs = ((~48, 44), 104);
    val locs =
      (ffun_offset + 0x2BB2,
      [ffun_offset + 0x2C12]);
  in
    birs_summary_gen
      (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x))
      (const_load_32_32_cheat_thms_fromprog ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x10000DA0+bin_offset1, 1))
      birs_prog_config
      [balrob_summary___aeabi_fmul_c4578brace_thm,
      balrob_summary___aeabi_fmul_c6_thm,
      balrob_summary___aeabi_fmul_c2brace_thm,
      balrob_summary___aeabi_fmul_c4578_thm] reqs locs
  end;


(* --------------------======================== BOT PART END ========================---------------- *)


(* TODO: uses one jump table encoded in manually extracted cfg! used to take 3 times as much time as sub or div *)
(* TODO: loads constants from memory! is the constant loading part of the lifting? better add some code to check this *)
val balrob_summary___aeabi_fmul_thm =
  let
    val reqs = ((0, 44), 244);
    val locs =
      (0x10000B44+bin_offset1,
      [0x10000C12+bin_offset1]);
  in
    birs_summary (*_gen
      (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x))
      (gen_const_load_32_32_cheat_thms [(0x10000DA0, 0x10000DA8)])*)
      birs_prog_config
      [balrob_summary___aeabi_fmul_part_top_thm,
      balrob_summary___aeabi_fmul_part_bot_thm]
      reqs
      locs
  end
Theorem balrob_summary___aeabi_fmul_thm =
  balrob_summary___aeabi_fmul_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
