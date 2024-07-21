open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aesTheory aes_specTheory;

val _ = new_theory "aes_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

val vars_of_prog_thm =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_aes_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_aes_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) vars_of_prog_thm;
val registervars = List.filter ((fn s => s <> "MEM8") o (stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)) all_vars;
val registervars_tm = listSyntax.mk_list (registervars, (type_of o hd) registervars);

Definition bir_aes_registervars_def:
 bir_aes_registervars = ^registervars_tm
End

val registervars_tm = (snd o dest_eq o concl) bir_aes_registervars_def;

Definition aes_prog_vars_def:
  aes_prog_vars = (BVar "MEM8" (BType_Mem Bit64 Bit8))::(^registervars_tm)
End

Definition aes_birenvtyl_def:
  aes_birenvtyl = MAP BVarToPair aes_prog_vars
End
(*
Theorem aes_prog_vars_thm:
  set aes_prog_vars = bir_vars_of_program (bir_aes_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_aes_prog_def, aes_prog_vars_def] >>
  EVAL_TAC
QED
*)

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_aes_prog_def
  aes_init_addr_def [aes_end_addr_def]
  bspec_aes_pre_def aes_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem aes_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
