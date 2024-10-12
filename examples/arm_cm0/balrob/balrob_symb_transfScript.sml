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
(* prepare for BIR property transfer *)
(* ------------------------------- *)
val bprog_envtyl_tm = (fst o dest_eq o concl) balrob_birenvtyl_def;
fun mk_bsysprecond_thm bspec_pre_tm bprog_envtyl_tm =
     (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
       (``mk_bsysprecond ^bspec_pre_tm ^bprog_envtyl_tm``);

(* TODO: need to instantiate "syp_gen" to true and remove that conjunct in the initial state before being able to transfer *)
(* TODO: need to bring hol variables for countw and SP into the initial pathcondition before this step *)
val pre_pcond_new_exp = (snd o dest_eq o snd o strip_forall o concl) bspec_balrob_clzsi2_pre_def;
val bsysprecond_thm = mk_bsysprecond_thm pre_pcond_new_exp bprog_envtyl_tm;
val bsysprecond_thm = REWRITE_RULE [GSYM bspec_balrob_clzsi2_pre_def] bsysprecond_thm;

val pre_pcond_new = (snd o dest_eq o concl) bsysprecond_thm;
val holvar_eq_exp = List.nth(birs_utilsLib.dest_band pre_pcond_new, 1);
(*
val _ = print_term holvar_eq_exp;
val _ = print "\n";
*)
val specd_symb_analysis_thm = birs_instantiationLib.birs_sound_symb_inst_RULE [(``BVar "syp_gen" (BType_Imm Bit1)``, holvar_eq_exp)] balrob_clzsi2_symb_analysis_thm;
val pcond_symb_analysis_thm = birs_utilsLib.birs_sys_pcond_RULE pre_pcond_new specd_symb_analysis_thm;
val fixed_symb_analysis_thm = REWRITE_RULE [GSYM bsysprecond_thm] pcond_symb_analysis_thm;

(*
val _ = print_thm bsysprecond_thm;
val _ = print "\n";
val _ = print "\n";
val _ = print_thm fixed_symb_analysis_thm;
val _ = print "\n";
val _ = print "\n";
val _ = raise Fail "";
*)

(* ------------------------------- *)
(* BIR property transfer *)
(* ------------------------------- *)
(*val _ = bir_smtLib.bir_smt_set_trace false 1;*)

(*
val _ = HOL_Interactive.toggle_quietdec();
val bir_prog_def = bir_balrob_prog_def;
val birenvtyl_def = balrob_birenvtyl_def;
val bspec_pre_def = bspec_balrob_clzsi2_pre_def;
val bspec_post_def = bspec_balrob_clzsi2_post_def;
val prog_vars_list_def = balrob_prog_vars_list_def;
val symb_analysis_thm = fixed_symb_analysis_thm;
(*val bsysprecond_thm = balrob_clzsi2_bsysprecond_thm;*)
val prog_vars_thm = balrob_prog_vars_thm;
val _ = HOL_Interactive.toggle_quietdec();
*)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_balrob_prog_def balrob_birenvtyl_def
  bspec_balrob_clzsi2_pre_def bspec_balrob_clzsi2_post_def balrob_prog_vars_list_def
  fixed_symb_analysis_thm bsysprecond_thm balrob_prog_vars_thm;

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
