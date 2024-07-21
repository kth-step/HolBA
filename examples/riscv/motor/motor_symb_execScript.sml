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

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_motor_prog_def
  motor_init_addr_def [motor_end_addr_def]
  bspec_motor_pre_def motor_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem motor_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
