open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open swapTheory;
open swap_specTheory;

val _ = new_theory "swap_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition swap_prog_vars_def:
  swap_prog_vars = [
    BVar "MEM8" (BType_Mem Bit64 Bit8);
    BVar "x15" (BType_Imm Bit64);
    BVar "x14" (BType_Imm Bit64);
    BVar "x11" (BType_Imm Bit64);
    BVar "x10" (BType_Imm Bit64);
    BVar "x1" (BType_Imm Bit64)
  ]
End

Definition swap_birenvtyl_def:
  swap_birenvtyl = MAP BVarToPair swap_prog_vars
End

Theorem swap_prog_vars_thm:
  set swap_prog_vars = bir_vars_of_program (bir_swap_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_swap_prog_def, swap_prog_vars_def] >>
  EVAL_TAC
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_swap_prog_def
  swap_init_addr_def [swap_end_addr_def]
  bspec_swap_pre_def swap_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem swap_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem swap_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
