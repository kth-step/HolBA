open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open chachaTheory;
open chacha_specTheory;
open chacha_symb_exec_column_roundTheory;

val _ = new_theory "chacha_symb_transf_column_round";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer_thm
  bir_chacha_prog_def
  chacha_column_round_init_addr_def chacha_column_round_end_addr_def
  bspec_chacha_column_round_pre_def bspec_chacha_column_round_post_def
  chacha_birenvtyl_def chacha_prog_vars_list_def
  chacha_column_round_symb_analysis_thm NONE chacha_prog_vars_thm;

val init_addr_tm = (snd o dest_eq o concl) chacha_column_round_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) chacha_column_round_end_addr_def;
val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_chacha_column_round_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_chacha_column_round_post_def;

Theorem bspec_cont_chacha_column_round:
 bir_cont bir_chacha_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bspec_cont_thm]
QED

val _ = export_theory ();
