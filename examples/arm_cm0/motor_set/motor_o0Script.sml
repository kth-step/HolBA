open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;

val _ = new_theory "motor_o0";

val birs_prog_config = ((fst o dest_eq o concl) motor_set_o0Lib.prog_def, motor_set_o0Lib.birenvtyl_def);

val bin_offset = 0x080000dc (*new*) - 0x10000000 (*old*);
val bin_offset2 = 0x08000120 (*new*) - 0x10000050 (*old*);

val gen_arg1 = (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x));
val gen_arg2 =
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) motorTheory.bir_o0_motor_progbin_def) (0x100000c8+bin_offset2, 0x100000dc+bin_offset2))@
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) motorTheory.bir_o0_motor_progbin_def) (0x10000154+bin_offset2, 0x10000168+bin_offset2));

val _ = set_default_cheat_setting ();

(* ------------------------------------ *)

val balrob_summary_motor_prep_input_thm =
  let
    val reqs = ((0, 24), 47);
    val locs =
      (0x10000000+bin_offset,
      [0x1000003e+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_prep_input_thm;
Theorem balrob_summary_motor_prep_input_thm =
  balrob_summary_motor_prep_input_thm;

(* ------------------------------------ *)

val balrob_summary_motor_set_l_thm =
  let
    val reqs = ((0, 24+24), 118);
    val locs =
      (0x10000050+bin_offset2,
      [0x100000c6+bin_offset2]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      [balrob_summary_motor_prep_input_thm]
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_set_l_thm;

(* ------------------------------------ *)

val balrob_summary_motor_set_r_thm =
  let
    val reqs = ((0, 24+24), 118);
    val locs =
      (0x100000dc+bin_offset2,
      [0x10000152+bin_offset2]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      [balrob_summary_motor_prep_input_thm]
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_set_r_thm;

(* ------------------------------------ *)

val balrob_summary_motor_set_thm =
  let
    val reqs = ((0, 24+24+16), 274);
    val locs =
      (0x10000168+bin_offset2,
      [0x10000188+bin_offset2]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      [balrob_summary_motor_set_l_thm,
       balrob_summary_motor_set_r_thm]
      reqs
      locs
  end;
Theorem balrob_summary_motor_set_thm =
  balrob_summary_motor_set_thm;
val _ = print_result balrob_summary_motor_set_thm ("0x8000258w", "pop {r7, pc}", "6");

(* ------------------------------------ *)

(* TODO: make sure that profiling contains a function that we want to measure *)
val _ = print "\n\nmotor_set o0 \"individual\" ran up to here\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)

val balrob_summary_motor_set_AIO_thm =
  let
    val reqs = ((0, 24+24+16), 274);
    val locs =
      (0x10000168+bin_offset2,
      [0x10000188+bin_offset2]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
Theorem balrob_summary_motor_set_AIO_thm =
  balrob_summary_motor_set_AIO_thm;
val _ = print_result balrob_summary_motor_set_AIO_thm ("0x8000258w", "pop {r7, pc}", "6");


(* ------------------------------------ *)

val _ = print "\n\nmotor_set o0 \"AIO\" ran up to here\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
