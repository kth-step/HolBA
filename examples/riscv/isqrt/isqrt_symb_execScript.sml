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
   BVar "x15" (BType_Imm Bit64);
   BVar "x14" (BType_Imm Bit64);
   BVar "x13" (BType_Imm Bit64);
   BVar "x10" (BType_Imm Bit64);
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

(* --------------------- *)
(* Symbolic precondition *)
(* --------------------- *)

(* FIXME: change to bspec_isqrt_pre once there is a bspec contract *)
Theorem isqrt_bsysprecond_thm =
 (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
 ``mk_bsysprecond (bir_isqrt_pre pre_x10) isqrt_birenvtyl``;

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_tm = (snd o dest_eq o concl) bir_isqrt_prog_def;
val init_addr_tm = (snd o dest_eq o concl) isqrt_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) isqrt_end_addr_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
val birs_state_end_lbls = [(snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))``];

val bprog_envtyl = (fst o dest_eq o concl) isqrt_birenvtyl_def;

val birs_pcond = (snd o dest_eq o concl) isqrt_bsysprecond_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val timer = bir_miscLib.timer_start 0;

val result = bir_symb_analysis bprog_tm
 birs_state_init_lbl birs_state_end_lbls
 bprog_envtyl birs_pcond;

val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n======\n > bir_symb_analysis took " ^ delta_s ^ "\n")) timer;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);

Theorem isqrt_symb_analysis_thm = result

val _ = export_theory ();
