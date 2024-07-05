open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open isqrtTheory isqrt_specTheory;

val _ = new_theory "isqrt_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition isqrt_prog_vars_def:
  isqrt_prog_vars = [
   BVar "MEM8" (BType_Mem Bit64 Bit8);
   BVar "x15" (BType_Imm Bit64);
   BVar "x14" (BType_Imm Bit64);
   BVar "x13" (BType_Imm Bit64);
   BVar "x10" (BType_Imm Bit64);
   BVar "x2" (BType_Imm Bit64);
   BVar "x1" (BType_Imm Bit64)]
End

Definition isqrt_birenvtyl_def:
  isqrt_birenvtyl = MAP BVarToPair isqrt_prog_vars
End

Theorem isqrt_prog_vars_thm:
  set isqrt_prog_vars = bir_vars_of_program (bir_isqrt_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_isqrt_prog_def, isqrt_prog_vars_def] >>
  EVAL_TAC
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ----------- *)
(* before loop *)
(* ----------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_1_def [isqrt_end_addr_1_def]
  bspec_isqrt_pre_1_def isqrt_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem isqrt_bsysprecond_1_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_1_thm = symb_analysis_thm

(* --------- *)
(* loop body *)
(* --------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_2_def [isqrt_end_addr_2_def]
  bspec_isqrt_pre_2_def isqrt_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem isqrt_bsysprecond_2_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_2_thm = symb_analysis_thm

(* ----------- *)
(* loop branch *)
(* ----------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_isqrt_prog_def
  isqrt_init_addr_3_def [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def]
  bspec_isqrt_pre_3_def isqrt_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem isqrt_bsysprecond_3_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem isqrt_symb_analysis_3_thm = symb_analysis_thm

val _ = export_theory ();
