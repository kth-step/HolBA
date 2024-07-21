open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open modexpTheory;
open modexp_specTheory;

val _ = new_theory "modexp_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Theorem modexp_prog_vars_thm0 =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_modexp_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_modexp_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) modexp_prog_vars_thm0;
val registervars_tm = listSyntax.mk_list (all_vars, (type_of o hd) all_vars);

Definition modexp_prog_vars_def:
  modexp_prog_vars = ^registervars_tm
End

Definition modexp_birenvtyl_def:
  modexp_birenvtyl = MAP BVarToPair modexp_prog_vars
End

Theorem modexp_prog_vars_thm:
  set modexp_prog_vars = bir_vars_of_program (bir_modexp_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [modexp_prog_vars_thm0, modexp_prog_vars_def]
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_modexp_prog_def
  modexp_init_addr_def [modexp_end_addr_def]
  bspec_modexp_pre_def modexp_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem modexp_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
