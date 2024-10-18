open HolKernel boolLib Parse bossLib;

open bir_immSyntax;

open bir_symbLib;

open birs_instantiationLib;
open birs_utilsLib;

open balrobLib;
open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_symb_transf";


val balrob_exec_thm = balrob_summary___clzsi2_thm;


(* TODO: the following could be extracted from the theorems above *)
(* TODO: move this after the symbolic execution, and infer the minimum and the maximum *)
val (countw_min, countw_max) = (21, 21);

val init_addr_tm = ``0x100013b4w : word32``;
val end_addr_tm = ``0x100013dcw : word32``;

val stack_max_usage = 77;
val reqs = (stack_max_usage, countw_max);
val balrob_pre = bslSyntax.bandl (pred_conjs reqs);


(* -------------- *)
(* BSPEC contract *)
(* -------------- *)
val bspec_balrob_pre_tm =
  bslSyntax.band (balrob_pre, bir_hvar_cond);

Definition bspec_balrob_pre_def:
  bspec_balrob_pre (pre_countw:word64) : bir_exp_t =
   ^bspec_balrob_pre_tm
End

val bspec_balrob_post_tm =
 bslSyntax.bandl [
 ``BExp_BinPred BIExp_LessOrEqual
       ^(mk_countw_plus bir_countw_hvar_tm countw_min)
       ^(bir_countw_bvar_tm)``,
 ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_plus bir_countw_hvar_tm countw_max)``
];
Definition bspec_balrob_post_def:
 bspec_balrob_post (pre_countw:word64) : bir_exp_t =
  ^bspec_balrob_post_tm
End


(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)
val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_balrob_pre_def;
val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_balrob_post_def;

(* ------------------------------- *)
(* make theorem for mk_bsysprecond fix *)
(* ------------------------------- *)
val birs_env_thm = gen_birs_env_thm balrob_birenvtyl_def;
val mk_bsysprecond_pcond_thm = gen_birs_pcond_thm balrob_birenvtyl_def bspec_pre_tm;
val birs_pcond_tm = (rhs o concl) mk_bsysprecond_pcond_thm;
val bir_hvar_cond_symb = gen_birs_pcond bir_hvar_cond;

(* ------------------------------- *)
(* prepare for BIR property transfer *)
(* ------------------------------- *)
val specd_symb_analysis_thm = birs_sound_symb_inst_RULE [(pcond_gen_symb, bir_hvar_cond_symb)] balrob_exec_thm;
val pcond_symb_analysis_thm = birs_sys_pcond_RULE birs_pcond_tm specd_symb_analysis_thm;
val pcond_symb_analysis_thm2 = CONV_RULE (birs_Pi_CONV (REWRITE_CONV [birs_auxTheory.BExp_IntervalPred_def])) pcond_symb_analysis_thm;
val fixed_symb_analysis_thm = CONV_RULE (birs_sys_CONV (REWRITE_CONV [GSYM mk_bsysprecond_pcond_thm, GSYM birs_env_thm])) pcond_symb_analysis_thm2;

(* ------------------------------- *)
(* BIR property transfer *)
(* ------------------------------- *)
(*val _ = bir_smtLib.bir_smt_set_trace false 1;*)

val balrob_prog_vars_thm = balrobTheory.balrob_prog_vars_thm;
val balrob_prog_vars_list_def = balrobTheory.balrob_prog_vars_list_def;

(*
val _ = HOL_Interactive.toggle_quietdec();
val bir_prog_def = bir_balrob_prog_def;
val birenvtyl_def = balrob_birenvtyl_def;
val bspec_pre_def = bspec_balrob_pre_def;
val bspec_post_def = bspec_balrob_post_def;
val prog_vars_list_def = balrob_prog_vars_list_def;
val symb_analysis_thm = fixed_symb_analysis_thm;
val bsysprecond_thm = mk_bsysprecond_pcond_thm;
val prog_vars_thm = balrob_prog_vars_thm;
val _ = HOL_Interactive.toggle_quietdec();
*)

val bspec_cont_thm =
 bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
  bir_balrob_prog_def balrob_birenvtyl_def
  bspec_balrob_pre_def bspec_balrob_post_def balrob_prog_vars_list_def
  fixed_symb_analysis_thm mk_bsysprecond_pcond_thm balrob_prog_vars_thm;

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
