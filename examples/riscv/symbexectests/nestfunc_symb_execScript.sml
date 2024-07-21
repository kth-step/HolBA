open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open nestfuncTheory;
open nestfunc_specTheory;

val _ = new_theory "nestfunc_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Theorem nestfunc_prog_vars_thm0 =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_nestfunc_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_nestfunc_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) nestfunc_prog_vars_thm0;
val registervars_tm = listSyntax.mk_list (all_vars, (type_of o hd) all_vars);

Definition nestfunc_prog_vars_def:
  nestfunc_prog_vars = ^registervars_tm
End

Definition nestfunc_birenvtyl_def:
  nestfunc_birenvtyl = MAP BVarToPair nestfunc_prog_vars
End

Theorem nestfunc_prog_vars_thm:
  set nestfunc_prog_vars = bir_vars_of_program (bir_nestfunc_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [nestfunc_prog_vars_thm0, nestfunc_prog_vars_def]
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_nestfunc_prog_def
  nestfunc_init_addr_def [nestfunc_end_addr_def]
  bspec_nestfunc_pre_def nestfunc_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem nestfunc_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
