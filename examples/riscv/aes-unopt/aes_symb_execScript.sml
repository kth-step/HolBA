open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aesTheory aes_specTheory;

val _ = new_theory "aes_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

val registervars_tm = (snd o dest_eq o concl) bir_aes_registervars_def;

Definition aes_prog_vars_def:
  aes_prog_vars = (BVar "MEM8" (BType_Mem Bit64 Bit8))::(^registervars_tm)
End

Definition aes_birenvtyl_def:
  aes_birenvtyl = MAP BVarToPair aes_prog_vars
End

Theorem aes_prog_vars_thm:
  set aes_prog_vars = bir_vars_of_program (bir_aes_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_aes_prog_def, aes_prog_vars_def] >>
  EVAL_TAC
QED

(* --------------------- *)
(* Symbolic precondition *)
(* --------------------- *)

Theorem aes_bsysprecond_thm =
 (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
 ``mk_bsysprecond bspec_aes_pre aes_birenvtyl``;

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_tm = (snd o dest_eq o concl) bir_aes_prog_def;
val init_addr_tm = (snd o dest_eq o concl) aes_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) aes_end_addr_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
val birs_state_end_lbls = [(snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))``];

val bprog_envtyl = (fst o dest_eq o concl) aes_birenvtyl_def;

val birs_pcond = (snd o dest_eq o concl) aes_bsysprecond_thm;

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

Theorem aes_symb_analysis_thm = result

val _ = export_theory ();
