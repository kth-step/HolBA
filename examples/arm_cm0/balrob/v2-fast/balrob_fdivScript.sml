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

(* ------------------------------------ *)

(* can speed this up by forgetting some stuff, the expressions grow pretty much here *)
val balrob_summary___aeabi_fdiv_loop_thm =
  let
    val balrob_summary___aeabi_fdiv_loop_body_thm =
      let
        val reqs = ((0, 0), 9);
        val locs =
          (0x10000734+bin_offset1,
          [0x10000746+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 381);
    val locs =
      (0x10000728+bin_offset1,
      [0x1000074A+bin_offset1]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fdiv_loop_body_thm] reqs locs
  end;

(* --------------------======================== TOP PART START ========================---------------- *)


val balrob_summary___aeabi_fdiv_part_top_thm =
  let
    val balrob_summary___aeabi_fdiv_c1_thm =
      let
        val reqs = ((0, 0), 15);
        val locs =
          (0x100005C2+bin_offset1,
          [0x100005D4+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 56);
    val locs =
      (0x100005BE+bin_offset1,
      [0x100005E6+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___clzsi2_thm,
       balrob_summary___aeabi_fdiv_c1_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fdiv_part_top_thm =
  balrob_summary___aeabi_fdiv_part_top_thm;
(*val _ = print "balrob_summary___aeabi_fdiv_part_top_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fdiv_part_top_thm;*)


(* --------------------======================== TOP PART END ========================---------------- *)

(* --------------------======================== BOTTOM PART START ========================---------------- *)

val balrob_summary___aeabi_fdiv_part_bot_thm =
  let
    val balrob_summary___aeabi_fdiv_c3_thm =
      let
        val balrob_summary___aeabi_fdiv_c4_thm =
          let
            val reqs = ((0, 0), 6);
            val locs =
              (0x10000648+bin_offset1,
              [0x10000652+bin_offset1]);
          in
            birs_summary birs_prog_config [] reqs locs
          end;

        val reqs = ((0, 0), 22);
        val locs =
          (0x1000063A+bin_offset1,
          [0x10000662+bin_offset1(*0x10000646*)]);
      in
        birs_summary birs_prog_config [balrob_summary___aeabi_fdiv_c4_thm] reqs locs
      end;
    (*val _ = print "balrob_summary___aeabi_fdiv_c3_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fdiv_c3_thm;*)

    val balrob_summary___aeabi_fdiv_c5_thm =
      let
        val balrob_summary___aeabi_fdiv_c6_thm =
          let
            val reqs = ((0, 0), 8);
            val locs =
              (0x1000079C+bin_offset1,
              [0x10000662+bin_offset1]);
          in
            birs_summary birs_prog_config [] reqs locs
          end;

        val reqs = ((0, 0), 16);
        val locs =
          (0x1000078E+bin_offset1,
          [0x10000662+bin_offset1(*0x1000079A*)]);
      in
        birs_summary birs_prog_config [balrob_summary___aeabi_fdiv_c6_thm] reqs locs
      end;
    (*val _ = print "balrob_summary___aeabi_fdiv_c5_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fdiv_c5_thm;*)

    val reqs = ((0, 0), 37);
    val locs =
      (0x10000630+bin_offset1,
      [0x10000662+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fdiv_c3_thm,
       balrob_summary___aeabi_fdiv_c5_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fdiv_part_bot_thm =
  balrob_summary___aeabi_fdiv_part_bot_thm;
(*val _ = print "balrob_summary___aeabi_fdiv_part_bot_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fdiv_part_bot_thm;*)

(* --------------------======================== BOTTOM PART END ========================---------------- *)

(* ------------------------------------ *)

val balrob_summary___aeabi_fdiv_c7_thm =
  let
    val reqs = ((0, 0), 15);
    val locs =
      (0x10000710+bin_offset1,
      [0x10000662+bin_offset1]);
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
      (0x100005A4+bin_offset1,
      [0x10000678+bin_offset1]);
  in
    birs_summary_gen
      (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x))
      ((const_load_32_32_cheat_thms_fromprog ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x100007bc+bin_offset1, 1))@
       (const_load_32_32_cheat_thms_fromprog ((rhs o concl) balrobTheory.bir_balrob_progbin_def) (0x100007c4+bin_offset1, 1)))
      birs_prog_config
      [balrob_summary___clzsi2_thm,
      balrob_summary___aeabi_fdiv_loop_thm,
      balrob_summary___aeabi_fdiv_part_top_thm,
      balrob_summary___aeabi_fdiv_part_bot_thm,
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
