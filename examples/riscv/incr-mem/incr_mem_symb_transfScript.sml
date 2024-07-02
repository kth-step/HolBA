open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open incr_memTheory;
open incr_mem_specTheory;
open incr_mem_symb_execTheory;

val _ = new_theory "incr_mem_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) incr_mem_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) incr_mem_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_incr_mem_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_incr_mem_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_incr_mem_prog_def incr_mem_birenvtyl_def
  bspec_incr_mem_pre_def bspec_incr_mem_post_def incr_mem_prog_vars_def
  incr_mem_symb_analysis_thm incr_mem_bsysprecond_thm incr_mem_prog_vars_thm;

Theorem bspec_cont_incr_mem:
 bir_cont bir_incr_mem_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_incr_mem_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
