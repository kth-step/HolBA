open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open kernel_trapTheory;
open kernel_trap_specTheory;
open kernel_trap_symb_execTheory;

val _ = new_theory "kernel_trap_return_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) kernel_trap_return_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) kernel_trap_return_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_kernel_trap_return_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_kernel_trap_return_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_kernel_trap_prog_def kernel_trap_birenvtyl_def
  bspec_kernel_trap_return_pre_def bspec_kernel_trap_return_post_def kernel_trap_prog_vars_list_def
  kernel_trap_return_symb_analysis_thm NONE kernel_trap_prog_vars_thm;

Theorem bspec_cont_kernel_trap_return:
 bir_cont bir_kernel_trap_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_kernel_trap_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
