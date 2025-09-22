open HolKernel Parse boolLib bossLib;

open birs_armcm0_supportLib;
open birs_armcm0_constmemLib;

val _ = new_theory "motor_o3";

val birs_prog_config = ((fst o dest_eq o concl) motor_set_o3Lib.prog_def, motor_set_o3Lib.birenvtyl_def);

val bin_offset = 0x08000204 (*new*) - 0x10000134 (*old*);

val gen_arg1 = (fn x => ((*print "\n\n"; print_term x; print "\n\n";*) birs_simpLib.birs_simp_ID_fun x));
val gen_arg2 =
  (const_load_32_32_cheat_thms_fromprog_range ((rhs o concl) motorTheory.bir_o3_motor_progbin_def) (0x10000214+bin_offset, 0x10000238+bin_offset));

val _ = set_default_cheat_setting ();

(* ------------------------------------ *)

val balrob_summary_motor_p1_thm =
  let
    val reqs = ((0, 0), 7);
    val locs =
      (0x100001d8+bin_offset,
      [0x100001da+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_p1_thm;
(* ------------------------------------ *)

val balrob_summary_motor_p2_thm =
  let
    val reqs = ((0, 0), 3);
    val locs =
      (0x10000164+bin_offset,
      [0x10000168+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_p2_thm;

(* ------------------------------------ *)

val balrob_summary_motor_p3_thm =
  let
    val reqs = ((0, 0), 7);
    val locs =
      (0x100001b2+bin_offset,
      [0x100001b4+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      []
      reqs
      locs
  end;
val _ = birs_find_countw_stack_usage balrob_summary_motor_p3_thm;

(* ------------------------------------ *)

val balrob_summary_motor_set_thm =
  let
    val reqs = ((0, 8), 90);
    val locs =
      (0x10000134+bin_offset,
      [0x10000184+bin_offset]);
  in
    birs_summary_gen
      gen_arg1
      gen_arg2
      birs_prog_config
      [balrob_summary_motor_p1_thm,
       balrob_summary_motor_p2_thm,
       balrob_summary_motor_p3_thm]
      reqs
      locs
  end;
Theorem balrob_summary_motor_set_thm =
  balrob_summary_motor_set_thm;
val _ = print_result balrob_summary_motor_set_thm ("0x8000254w", "pop {r4, pc}", "6");

(* ------------------------------------ *)

val _ = print "\n\nmotor_set o3 \"individual\" ran up to here\n";
val _ = Profile.print_profile_results (Profile.results ());

(* ------------------------------------ *)

val balrob_summary_motor_set_AIO_thm =
  let
    val reqs = ((0, 8), 90);
    val locs =
      (0x10000134+bin_offset,
      [0x10000184+bin_offset]);
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
val _ = print_result balrob_summary_motor_set_AIO_thm ("0x8000254w", "pop {r4, pc}", "6");


(* ------------------------------------ *)

val _ = print "\n\nmotor_set o3 \"AIO\" ran up to here\n";
val _ = Profile.print_profile_results (Profile.results ());


val _ = export_theory ();
