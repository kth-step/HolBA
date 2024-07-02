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

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_def = bir_swap_prog_def;
val init_addr_def = swap_init_addr_def;
val end_addr_def = swap_end_addr_def;
val bspec_pre_def = bspec_swap_pre_def;
val bprog_birenvtyl_def = swap_birenvtyl_def;

val bprog_tm = (snd o dest_eq o concl) bprog_def;
val init_addr_tm = (snd o dest_eq o concl) init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) end_addr_def;
val birs_state_init_lbl_tm = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
val birs_state_end_lbls_tm = [(snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))``];
val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_pre_def;
val bprog_envtyl_tm = (fst o dest_eq o concl) bprog_birenvtyl_def;

(* --------------------- *)
(* Symbolic precondition *)
(* --------------------- *)

Theorem swap_bsysprecond_thm =
 (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
 ``mk_bsysprecond ^bspec_pre_tm ^bprog_envtyl_tm``;

val birs_pcond_tm = (snd o dest_eq o concl) swap_bsysprecond_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val timer = bir_miscLib.timer_start 0;

val result = bir_symb_analysis bprog_tm
 birs_state_init_lbl_tm birs_state_end_lbls_tm
 bprog_envtyl_tm birs_pcond_tm;

val _ = bir_miscLib.timer_stop
 (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n"))
 timer;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);

Theorem swap_symb_analysis_thm = result

val _ = export_theory ();
