open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;

open modexp_asm_uidivmodTheory;

val _ = new_theory "modexp_asm";

val birs_prog_config = ((fst o dest_eq o concl) modexp_asmLib.prog_def, modexp_asmLib.birenvtyl_def);

val _ = set_default_cheat_setting ();

val bin_offset = 0x08008070 (*new*) - 0x10000240 (*old*);

(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)

val balrob_summary__my_modexp_asm_loop_thm =
  let
    val reqs = ((~20, 20+32+16), 6170); (* TODO: why need 16 more for stack? *)
    val locs =
      (0x10000300+bin_offset(*0x10000306*),
      [0x10000338+bin_offset(*0x10000302*)]);
  in
    birs_summary birs_prog_config [balrob_summary__my_uidivmod_mod_asm_thm] reqs locs
  end;
(*
val _ = print "\n\nLOOP BODY DONE\n\n"
val _ = print_thm balrob_summary__my_modexp_asm_loop_thm;
val _ = print "\n\nLOOP BODY PRINT DONE\n\n"
*)
val _ = birs_find_countw_stack_usage balrob_summary__my_modexp_asm_loop_thm;
Theorem balrob_summary__my_modexp_asm_loop_thm =
  balrob_summary__my_modexp_asm_loop_thm;


val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)

val balrob_summary__my_modexp_asm_thm =
  let
    val reqs = ((0, 68), 197557);
    val locs =
      (0x100002f0+bin_offset,
      [0x10000344+bin_offset(*0x10000300, 0x10000344*)]);
  in
    birs_summary birs_prog_config [balrob_summary__my_modexp_asm_loop_thm] reqs locs
  end;
Theorem balrob_summary__my_modexp_asm_thm =
  balrob_summary__my_modexp_asm_thm;
val _ = print_result balrob_summary__my_modexp_asm_thm ("0x8008174w", "bx lr", "3");


(* ------------------------------------ *)

val _ = print "\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
