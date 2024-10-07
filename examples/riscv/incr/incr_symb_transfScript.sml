open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open incrTheory;
open incr_specTheory;
open incr_symb_execTheory;

val _ = new_theory "incr_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) incr_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) incr_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_incr_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_incr_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

(*
val bir_prog_def  = bir_incr_prog_def;
val birenvtyl_def = incr_birenvtyl_def;
val bspec_pre_def = bspec_incr_pre_def;
val bspec_post_def = bspec_incr_post_def;
val prog_vars_list_def = incr_prog_vars_list_def;
val symb_analysis_thm  = incr_symb_analysis_thm;
val bsysprecond_thm  = incr_bsysprecond_thm;
val prog_vars_thm = incr_prog_vars_thm;
*)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_incr_prog_def incr_birenvtyl_def
  bspec_incr_pre_def bspec_incr_post_def incr_prog_vars_list_def
  incr_symb_analysis_thm incr_bsysprecond_thm incr_prog_vars_thm;

Theorem bspec_cont_incr:
 bir_cont bir_incr_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_incr_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
