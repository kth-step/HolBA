open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open mod2Theory mod2_specTheory;

val _ = new_theory "mod2_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition mod2_prog_vars_def:
  mod2_prog_vars = [BVar "x10" (BType_Imm Bit64); BVar "x1" (BType_Imm Bit64)]
End

Definition mod2_birenvtyl_def:
  mod2_birenvtyl = MAP BVarToPair mod2_prog_vars
End

Theorem mod2_prog_vars_thm:
  set mod2_prog_vars = bir_vars_of_program (bir_mod2_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_mod2_prog_def, mod2_prog_vars_def] >>
  EVAL_TAC
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val timer = bir_miscLib.timer_start 0;

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_mod2_prog_def
  mod2_init_addr_def [mod2_end_addr_def]
  bspec_mod2_pre_def mod2_birenvtyl_def;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem mod2_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem mod2_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
