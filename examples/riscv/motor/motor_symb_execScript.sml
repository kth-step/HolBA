open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open motorTheory;
open motor_specTheory;

val _ = new_theory "motor_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Theorem motor_prog_vars_thm0 =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_motor_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_motor_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) motor_prog_vars_thm0;
val registervars_tm = listSyntax.mk_list (all_vars, (type_of o hd) all_vars);

Definition motor_prog_vars_def:
  motor_prog_vars = ^registervars_tm
End

Definition motor_birenvtyl_def:
  motor_birenvtyl = MAP BVarToPair motor_prog_vars
End

Theorem motor_prog_vars_thm:
  set motor_prog_vars = bir_vars_of_program (bir_motor_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [motor_prog_vars_thm0, motor_prog_vars_def]
QED

(* --------------------- *)
(* Symbolic precondition *)
(* --------------------- *)

Theorem motor_bsysprecond_thm =
 (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
 ``mk_bsysprecond (bspec_motor_pre pre_x2) motor_birenvtyl``;

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_tm = (snd o dest_eq o concl) bir_motor_prog_def;
val init_addr_tm = (snd o dest_eq o concl) motor_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) motor_end_addr_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
val birs_state_end_lbls = [(snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))``];

val bprog_envtyl = (fst o dest_eq o concl) motor_birenvtyl_def;

val birs_pcond = (snd o dest_eq o concl) motor_bsysprecond_thm;

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

Theorem motor_symb_analysis_thm = result

val _ = export_theory ();
