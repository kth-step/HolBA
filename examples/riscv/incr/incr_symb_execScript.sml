open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open incrTheory;
open incr_specTheory;

val _ = new_theory "incr_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition incr_prog_vars_def:
  incr_prog_vars = [BVar "x10" (BType_Imm Bit64); BVar "x1" (BType_Imm Bit64)]
End

Definition incr_birenvtyl_def:
  incr_birenvtyl = MAP BVarToPair incr_prog_vars
End

Theorem incr_prog_vars_thm:
  set incr_prog_vars = bir_vars_of_program (bir_incr_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_incr_prog_def, incr_prog_vars_def]
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thms
  bir_incr_prog_def
  incr_init_addr_def incr_end_addr_def
  bspec_incr_pre_def incr_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem incr_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem incr_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
