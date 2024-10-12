open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_immSyntax;

open bir_symbLib;
open birs_instantiationLib;
open birs_utilsLib;

open balrobLib;
open balrob_endsTheory;

val _ = new_theory "balrob_symb_transf";


val balrob_exec_thm = balrob_clzsi2_symb_exec_thm;
(*val bsysprecond_thm = balrob_clzsi2_bsysprecond_thm;*)
val birs_env_thm = balrob_clzsi2_birs_env_thm;
(**)
val bprog_envtyl_tm = (fst o dest_eq o concl) balrob_birenvtyl_def;
(* TODO: the following can be extracted from the theorems above *)
val init_addr_tm = ``0x100013b4w : word32``;
val end_addr_tm = ``0x100013dcw : word32``;
val balrob_pre = ``BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0xFFFFFEBw))``;

(* TODO: move this after the symbolic execution, and infer the minimum and the maximum *)
val (countw_min, countw_max) = (21, 21);

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)
val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
val bir_countw_hvar_tm = ``BExp_Const (Imm64 pre_countw)``;
fun mk_countw_const v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
fun mk_countw_plus tm v = bslSyntax.bplus (tm, mk_countw_const v);
val bir_hvar_cond = bslSyntax.beq (bir_countw_bvar_tm, bir_countw_hvar_tm);

val bspec_balrob_pre_tm =
  ``BExp_BinExp BIExp_And
   ^balrob_pre
   ^bir_hvar_cond``;

Definition bspec_balrob_pre_def:
  bspec_balrob_pre (pre_countw:word64) : bir_exp_t =
   ^bspec_balrob_pre_tm
End

(* TODO: make this an interval statement *)
val bspec_balrob_post_tm = bslSyntax.bandl [
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
fun create_mk_bsysprecond_thm t =
  (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
    (``mk_bsysprecond ^t ^bprog_envtyl_tm``);
val mk_bsysprecond_pcond_thm = create_mk_bsysprecond_thm bspec_pre_tm;
val birs_pcond_tm = (snd o dest_eq o concl) mk_bsysprecond_pcond_thm;
val bir_hvar_cond_symb = (snd o dest_eq o concl o create_mk_bsysprecond_thm) bir_hvar_cond;

(* ------------------------------- *)
(* prepare for BIR property transfer *)
(* ------------------------------- *)
val specd_symb_analysis_thm = birs_sound_symb_inst_RULE [(``BVar "syp_gen" (BType_Imm Bit1)``, bir_hvar_cond_symb)] balrob_exec_thm;
val pcond_symb_analysis_thm = birs_sys_pcond_RULE birs_pcond_tm specd_symb_analysis_thm;
val fixed_symb_analysis_thm = CONV_RULE (birs_sys_CONV (REWRITE_CONV [GSYM mk_bsysprecond_pcond_thm, GSYM birs_env_thm])) pcond_symb_analysis_thm;

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
