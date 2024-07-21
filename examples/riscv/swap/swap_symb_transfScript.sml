open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open swapTheory;
open swap_specTheory;
open swap_symb_execTheory;

val _ = new_theory "swap_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) swap_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) swap_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_swap_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_swap_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_swap_prog_def swap_birenvtyl_def
  bspec_swap_pre_def bspec_swap_post_def swap_prog_vars_list_def
  swap_symb_analysis_thm swap_bsysprecond_thm swap_prog_vars_thm;

Theorem bspec_cont_swap:
 bir_cont bir_swap_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_swap_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
