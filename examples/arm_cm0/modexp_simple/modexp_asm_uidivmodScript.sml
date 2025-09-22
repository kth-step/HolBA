open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

val _ = new_theory "modexp_asm_uidivmod";

val birs_prog_config = ((fst o dest_eq o concl) modexp_asmLib.prog_def, modexp_asmLib.birenvtyl_def);

val _ = set_default_cheat_setting ();

val bin_offset = 0x08008070 (*new*) - 0x10000240 (*old*);

val alt_sp_bvar_analysis_tm = ``BExp_Den (BVar "R7" (BType_Imm Bit32))``;

(* ------------------------------------ *)

val _ = alt_sp_bvar_tm := SOME alt_sp_bvar_analysis_tm;
val balrob_summary__my_uidivmod_mod_asm_loop1_body_thm =
  let
    val reqs = ((~32, 32), 38);
    val locs =
      (0x1000025c+bin_offset,
      [0x10000290+bin_offset]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary__my_uidivmod_mod_asm_loop1_body_thm;
val balrob_summary__my_uidivmod_mod_asm_loop2_body_thm =
  let
    val reqs = ((~32, 32), 48);
    val locs =
      (0x1000029e+bin_offset,
      [0x100002dc+bin_offset]);
  in
    birs_summary birs_prog_config [] reqs locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary__my_uidivmod_mod_asm_loop2_body_thm;
val _ = alt_sp_bvar_tm := NONE;

val (_, mem_exp) = (birsSyntax.get_birs_Pi_first_env_top_mapping o concl o CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV "MEM"))) balrob_summary__my_uidivmod_mod_asm_loop2_body_thm;
val _ = birs_mergeLib.print_mem_exp 700 mem_exp;

val balrob_summary__my_uidivmod_mod_asm_thm =
  let
    val reqs = ((0, 32), 3054);
    val locs =
      (0x10000240+bin_offset,
      [0x100002e8+bin_offset]);
  in
    birs_summary
      birs_prog_config
      [balrob_summary__my_uidivmod_mod_asm_loop1_body_thm,
       balrob_summary__my_uidivmod_mod_asm_loop2_body_thm]
      reqs
      locs
  end;
Theorem balrob_summary__my_uidivmod_mod_asm_thm =
  balrob_summary__my_uidivmod_mod_asm_thm;
val _ = print_result balrob_summary__my_uidivmod_mod_asm_thm ("0x8008118w", "pop {r7, pc}", "6");

(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
