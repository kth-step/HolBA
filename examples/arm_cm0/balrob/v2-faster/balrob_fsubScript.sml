open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fsub";

val birs_prog_config = balrobLib.birs_prog_config;

val _ = set_default_cheat_setting ();

val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)

(* --------------------======================== CONNECTED IN THE BOTTOM ========================---------------- *)

val balrob_summary___aeabi_fsub_bot01_thm =
  let
    val reqs = ((0, 0), 13);
    val locs =
      (0x10000FDE+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_bot01_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_bot01_thm;*)

val balrob_summary___aeabi_fsub_bot02_thm =
  let
    val reqs = ((0, 0), 18);
    val locs =
      (0x10000FF6+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fsub_bot01_thm] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_bot02_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_bot02_thm;*)

val balrob_summary___aeabi_fsub_c2_thm =
  let
    val reqs = ((0, 0), 22);
    val locs =
      (0x10000EF0+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fsub_bot02_thm] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_c2_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_c2_thm;*)

val balrob_summary___aeabi_fsub_c7_thm =
  let
    val reqs = ((0, 0), 26);
    val locs =
      (0x10000EEA+bin_offset1,
      [0x10000F02+bin_offset1 (*0x10000EEE*)]);
  in
    birs_summary birs_prog_config [balrob_summary___aeabi_fsub_c2_thm] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_c7_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_c7_thm;*)

(* --------------------======================== STANDALONE BRANCH AND MERGE ========================---------------- *)

val balrob_summary___aeabi_fsub_c1_thm =
  let
    val reqs = ((0, 0), 13);
    val locs =
      (0x10000E7C+bin_offset1,
      [0x10000E84+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c3_thm =
  let
    val reqs = ((0, 0), 11);
    val locs =
      (0x10000F56+bin_offset1,
      [0x10000F6C+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c4_thm =
  let
    val reqs = ((0, 0), 9);
    val locs =
      (0x10001112+bin_offset1,
      [0x10001124+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c5_thm =
  let
    val reqs = ((0, 0), 11);
    val locs =
      (0x10001016+bin_offset1,
      [0x1000102A+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* ------------------------------------ *)

val balrob_summary___aeabi_fsub_c6_thm =
  let
    val reqs = ((0, 0), 6);
    val locs =
      (0x1000115C+bin_offset1,
      [0x10001168+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;

(* --------------------======================== NEW BRANCH AND MERGE ========================---------------- *)

val balrob_summary___aeabi_fsub_s1_thm =
  let
    val reqs = ((0, 0), 9);
    val locs =
      (0x10001140+bin_offset1,
      [0x10000FDC+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_s1_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_s1_thm;*)

val balrob_summary___aeabi_fsub_s2_thm =
  let
    val reqs = ((0, 0), 15);
    val locs =
      (0x10000FA2+bin_offset1,
      [0x10000FC0+bin_offset1]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_s2_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_s2_thm;*)

(* --------------------======================== BOTTOM COLLECTIONS ========================---------------- *)

val balrob_summary___aeabi_fsub_bot1_thm =
  let
    val reqs = ((0, 0), 36);
    val locs =
      (0x10000FC6+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fsub_c7_thm,
       balrob_summary___aeabi_fsub_bot02_thm]
      reqs
      locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_bot1_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_bot1_thm;*)

val balrob_summary___aeabi_fsub_bot2_thm =
  let
    val reqs = ((0, 0), 53);
    val locs =
      (0x10000F6E+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fsub_bot1_thm,
       balrob_summary___aeabi_fsub_c7_thm]
      reqs
      locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_bot2_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_bot2_thm;*)

val balrob_summary___aeabi_fsub_bot3_thm =
  let
    val balrob_summary___aeabi_fsub_c8_thm =
      let
        val reqs = ((0, 0), 16);
        val locs =
          (0x10000EBC+bin_offset1,
          [0x10000EDA+bin_offset1]);
      in
        birs_summary birs_prog_config [] reqs locs
      end;

    val reqs = ((0, 0), 82);
    val locs =
      (0x10000EB0+bin_offset1,
      [0x10000F02+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___clzsi2_thm,
       balrob_summary___aeabi_fsub_c8_thm,
       balrob_summary___aeabi_fsub_c7_thm,
       balrob_summary___aeabi_fsub_c2_thm]
      reqs
      locs
  end;
(*val _ = print "balrob_summary___aeabi_fsub_bot3_thm\n";
val _ = print "--------------------------\n";
val _ = (print_term o birsSyntax.get_birs_Pi_first_pcond o concl) balrob_summary___aeabi_fsub_bot3_thm;*)


(* ------------------------------------ *)


(* FFFE090 *)
val balrob_summary___aeabi_fsub_thm =
  let
    val reqs = ((0, 32), 187);
    val locs =
      (0x10000E50+bin_offset1,
      [0x10000F14+bin_offset1]);
  in
    birs_summary birs_prog_config
      [balrob_summary___aeabi_fsub_c1_thm,
       balrob_summary___aeabi_fsub_c2_thm,
       balrob_summary___aeabi_fsub_c3_thm,
       balrob_summary___aeabi_fsub_c4_thm,
       balrob_summary___aeabi_fsub_c5_thm,
       balrob_summary___aeabi_fsub_c6_thm,
       balrob_summary___aeabi_fsub_c7_thm,
       balrob_summary___aeabi_fsub_bot01_thm,
       balrob_summary___aeabi_fsub_bot02_thm,
       balrob_summary___aeabi_fsub_s1_thm,
       balrob_summary___aeabi_fsub_s2_thm,
       balrob_summary___aeabi_fsub_bot1_thm,
       balrob_summary___aeabi_fsub_bot2_thm,
       balrob_summary___aeabi_fsub_bot3_thm]
      reqs
      locs
  end;
Theorem balrob_summary___aeabi_fsub_thm =
  balrob_summary___aeabi_fsub_thm;


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)


val _ = run_default_postproc ();

val _ = export_theory ();
