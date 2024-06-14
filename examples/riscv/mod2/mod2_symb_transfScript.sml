open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open mod2Theory;
open mod2_specTheory;
open mod2_symb_execTheory;

val _ = new_theory "mod2_symb_transf";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) mod2_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) mod2_end_addr_def;

val bspec_pre_tm = ``bspec_mod2_pre pre_x10``;
val bspec_post_tm = ``bspec_mod2_post pre_x10``;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_mod2_prog_def mod2_birenvtyl_def bspec_mod2_pre_def bspec_mod2_post_def mod2_prog_vars_def
  mod2_symb_analysis_thm mod2_bsysprecond_thm mod2_prog_vars_thm;

Theorem bspec_cont_mod2:
 bir_cont bir_mod2_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bir_mod2_prog_def,bspec_cont_thm]
QED

val _ = export_theory ();
