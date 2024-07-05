open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open incr_memTheory;
open incr_mem_specTheory;

val _ = new_theory "incr_mem_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition incr_mem_prog_vars_def:
  incr_mem_prog_vars = [
   BVar "MEM8" (BType_Mem Bit64 Bit8);
   BVar "x15" (BType_Imm Bit64);
   BVar "x10" (BType_Imm Bit64);
   BVar "x1" (BType_Imm Bit64)]
End

Definition incr_mem_birenvtyl_def:
  incr_mem_birenvtyl = MAP BVarToPair incr_mem_prog_vars
End

Theorem incr_mem_prog_vars_thm:
  set incr_mem_prog_vars = bir_vars_of_program (bir_incr_mem_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_incr_mem_prog_def, incr_mem_prog_vars_def] >> EVAL_TAC
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thms
  bir_incr_mem_prog_def
  incr_mem_init_addr_def incr_mem_end_addr_def
  bspec_incr_mem_pre_def incr_mem_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem incr_mem_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem incr_mem_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
