open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fadd";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)

(* split strategy, first bottom, then left then right *)

(* --------------------======================== BOT PART START ========================---------------- *)

val balrob_summary___aeabi_fadd_c3_thm =
  let
    val reqs = ((0, 0), 17);
    val locs =
      (0x10000248+bin_offset1, (*0x10000364,*)
      [0x10000256+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fadd_c2_thm =
  let
    val reqs = ((0, 0), 33);
    val locs =
      (0x1000032C+bin_offset1, (*0x10000334,*)
      [0x10000256+bin_offset1]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fadd_c3_thm] reqs locs
  end;

val balrob_summary___aeabi_fadd_c1_thm =
  let
    val reqs = ((0, 0), 35);
    val locs =
      (0x100003B6+bin_offset1,
      [0x10000256+bin_offset1]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fadd_c3_thm] reqs locs
  end;

(* --------------------======================== BOT PART END ========================---------------- *)

(* --------------------======================== LEFT PART START ========================---------------- *)

val balrob_summary___aeabi_fadd_part_left_thm =
  let
    val balrob_summary___aeabi_fadd_part_left1_thm =
      let
        val reqs = ((0, 0), 51);
        val locs =
          (0x100002BC+bin_offset1,
          [0x10000256+bin_offset1]);
      in
        birs_summary birs_prog_config
          [balrob_summary___aeabi_fadd_c1_thm,
          balrob_summary___aeabi_fadd_c2_thm]
          reqs
          locs
      end;

    val balrob_summary___aeabi_fadd_part_left2_thm =
      let
        val reqs = ((0, 0), 48);
        val locs =
          (0x1000046A+bin_offset1,
          [0x10000256+bin_offset1]);
      in
        birs_summary birs_prog_config
          [balrob_summary___aeabi_fadd_c1_thm,
          balrob_summary___aeabi_fadd_c2_thm]
          reqs
          locs
      end;

    val balrob_summary___aeabi_fadd_part_left_top1_thm =
      let
        val reqs = ((0, 0), 12);
        val locs =
          (0x100002A4+bin_offset1,
          [0x100002BA+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val balrob_summary___aeabi_fadd_part_left_top2_thm =
      let
        val reqs = ((0, 0), 14);
        val locs =
          (0x10000494+bin_offset1,
          [0x100002BA+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val balrob_summary___aeabi_fadd_part_left_top3_thm =
      let
        val reqs = ((0, 0), 6);
        val locs =
          (0x100004BE+bin_offset1,
          [0x100004C8+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 88);
    val locs =
      (0x10000290+bin_offset1,
      [0x10000256+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fadd_part_left_top1_thm,
       balrob_summary___aeabi_fadd_part_left_top2_thm,
       balrob_summary___aeabi_fadd_part_left_top3_thm,
       balrob_summary___aeabi_fadd_part_left1_thm,
       balrob_summary___aeabi_fadd_part_left2_thm,
       balrob_summary___aeabi_fadd_c2_thm,
       balrob_summary___aeabi_fadd_c3_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fadd_part_left_thm =
  balrob_summary___aeabi_fadd_part_left_thm;


(* --------------------======================== LEFT PART END ========================---------------- *)

(* --------------------======================== RIGHT PART END ========================---------------- *)

val balrob_summary___aeabi_fadd_part_right_thm =
  let
    val balrob_summary___aeabi_fadd_part_right2_thm =
      let
        val balrob_summary___aeabi_fadd_part_right1_thm =
          let
            val reqs = ((0, 0), 37);
            val locs =
              (0x100004E8+bin_offset1,
              [0x10000256+bin_offset1]);
          in
            birs_summary birs_prog_config
              [balrob_summary___aeabi_fadd_c3_thm]
              reqs
              locs
          end;
        (*val _ = print "balrob_summary___aeabi_fadd_part_right1_thm\n";
        val _ = print "--------------------------\n";
        val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right1_thm;*)

        val reqs = ((0, 0), 58);
        val locs =
          (0x10000278+bin_offset1,
          [0x10000256+bin_offset1]);
      in
        birs_summary birs_prog_config
          [balrob_summary___aeabi_fadd_part_right1_thm,
           balrob_summary___aeabi_fadd_c1_thm,
           balrob_summary___aeabi_fadd_c2_thm,
           balrob_summary___aeabi_fadd_c3_thm]
          reqs
          locs
      end;
    (*val _ = print "balrob_summary___aeabi_fadd_part_right2_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right2_thm;*)

    val balrob_summary___aeabi_fadd_part_right3_thm =
      let
        val reqs = ((0, 0), 80);
        val locs =
          (0x10000302+bin_offset1,
          [0x10000256+bin_offset1]);
      in
        birs_summary birs_prog_config
          [balrob_summary___clzsi2_thm,
           balrob_summary___aeabi_fadd_c2_thm]
          reqs
          locs
      end;
    (*val _ = print "balrob_summary___aeabi_fadd_part_right3_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right3_thm;*)

    val balrob_summary___aeabi_fadd_part_right_top1_thm =
      let
        val reqs = ((0, 0), 11);
        val locs =
          (0x100002E4+bin_offset1,
          [0x100002F8+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;
    (*val _ = print "balrob_summary___aeabi_fadd_part_right_top1_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right_top1_thm;*)

    (*val balrob_summary___aeabi_fadd_part_right_top2_thm =
      let
        val reqs = ((0, 0), 100);
        val locs =
          (0x1000027E,
          [0x10000302]); (* NOTE: this is wrong!!! *)
      in
        birs_summary birs_prog_config [] reqs locs
      end;
    val _ = print "balrob_summary___aeabi_fadd_part_right_top2_thm\n";
    val _ = print "--------------------------\n";
    val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right_top2_thm;*)

    val reqs = ((0, 0), 125);
    val locs =
      (0x1000023C+bin_offset1,
      [0x10000256+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fadd_part_right_top1_thm,
       (*balrob_summary___aeabi_fadd_part_right_top2_thm,*)
       balrob_summary___aeabi_fadd_part_right2_thm,
       balrob_summary___aeabi_fadd_part_right3_thm,
       balrob_summary___aeabi_fadd_c1_thm,
       balrob_summary___aeabi_fadd_c3_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fadd_part_right_thm =
  balrob_summary___aeabi_fadd_part_right_thm;
(*val _ = print "balrob_summary___aeabi_fadd_part_right_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fadd_part_right_thm;*)



(* --------------------======================== RIGHT PART END ========================---------------- *)

(* ------------------------------------ *)


val balrob_summary___aeabi_fadd_thm =
  let
    val reqs = ((0, 32), 168);
    val locs =
      (0x1000020c+bin_offset1,
      [0x10000268+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fadd_part_left_thm,
       balrob_summary___aeabi_fadd_part_right_thm]
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
