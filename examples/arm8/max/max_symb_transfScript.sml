open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open maxTheory;
open max_spec_arm8Theory;
open max_spec_birTheory;
open max_symb_execTheory;

val _ = new_theory "max_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) max_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) max_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_max_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_max_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_max_prog_def max_birenvtyl_def
  bspec_max_pre_def bspec_max_post_def max_prog_vars_list_def
  max_symb_analysis_thm NONE max_prog_vars_thm;

Theorem bspec_cont_max:
 bir_cont bir_max_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_max_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
