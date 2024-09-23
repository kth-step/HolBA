open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_immSyntax;

open bir_symbLib;

open balrobLib;
open balrob_endsTheory;

val _ = new_theory "balrob_symb_transf";
val balrob_prog_vars_thm = balrobTheory.balrob_prog_vars_thm;
val balrob_prog_vars_list_def = balrobTheory.balrob_prog_vars_list_def;

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val init_addr_tm = (snd o dest_eq o concl) balrob_clzsi2_init_addr_def;
val end_addr_tm = (snd o dest_eq o concl) balrob_clzsi2_end_addr_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_balrob_clzsi2_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_balrob_clzsi2_post_def;

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)
(*val _ = bir_smtLib.bir_smt_set_trace false 1;*)

(*
val _ = HOL_Interactive.toggle_quietdec();
val bir_prog_def = bir_balrob_prog_def;
val birenvtyl_def = balrob_birenvtyl_def;
val bspec_pre_def = bspec_balrob_clzsi2_pre_def;
val bspec_post_def = bspec_balrob_clzsi2_post_def;
val prog_vars_list_def = balrob_prog_vars_list_def;
val symb_analysis_thm = balrob_clzsi2_symb_analysis_thm;
val bsysprecond_thm = balrob_clzsi2_bsysprecond_thm;
val prog_vars_thm = balrob_prog_vars_thm;
val _ = HOL_Interactive.toggle_quietdec();
*)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_balrob_prog_def balrob_birenvtyl_def
  bspec_balrob_clzsi2_pre_def bspec_balrob_clzsi2_post_def balrob_prog_vars_list_def
  balrob_clzsi2_symb_analysis_thm balrob_clzsi2_bsysprecond_thm balrob_prog_vars_thm;

Theorem bspec_cont_balrob:
 bir_cont bir_balrob_prog bir_exp_true
  (BL_Address ^(gen_mk_Imm init_addr_tm)) {BL_Address ^(gen_mk_Imm end_addr_tm)} {}
  ^bspec_pre_tm
  (\l. if l = BL_Address ^(gen_mk_Imm end_addr_tm)
       then ^bspec_post_tm
       else bir_exp_false)
Proof
 rw [bspec_cont_thm]
QED

val _ = export_theory ();
