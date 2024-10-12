open HolKernel Parse boolLib bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_predLib;

open bir_symbLib;

open birs_mergeLib;
open birs_instantiationLib;
open birs_composeLib;

open balrobLib;
open balrob_ends_mergeTheory;

val _ = new_theory "balrob_insttest";

(* instantiation test *)

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition balrob_insttest_init_addr_def:
 balrob_insttest_init_addr : word32 = 0x100012d6w
End

Definition balrob_insttest_end_addr_def:
 balrob_insttest_end_addr : word32 = 0x100013b4w
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)
val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
fun mk_countw_const v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
fun mk_countw_plus tm v = bslSyntax.bplus (tm, mk_countw_const v);

(* commonBalrobScriptLib.sml *)
val countw_space_req = 63;
val bspec_balrob_insttest_pre_tm = 
  ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_const (0x10000000 - countw_space_req))``;

Definition bspec_balrob_insttest_pre_def:
  bspec_balrob_insttest_pre (pre_countw:word64) : bir_exp_t =
   ^bspec_balrob_insttest_pre_tm
End


(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm_gen
  NONE
  bir_balrob_prog_def
  balrob_insttest_init_addr_def [balrob_insttest_end_addr_def]
  bspec_balrob_insttest_pre_def balrob_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem balrob_insttest_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem balrob_insttest_symb_analysis_thm = symb_analysis_thm

(*
val _ = print_thm balrob_clzsi2_symb_merged_thm;
val _ = raise Fail "";
*)
val birenvtyl_def = balrob_birenvtyl_def;
val bprog_envtyl_tm = (fst o dest_eq o concl) birenvtyl_def;
val birs_env_thm = (REWRITE_CONV [birenvtyl_def] THENC EVAL THENC REWRITE_CONV [GSYM birs_auxTheory.birs_gen_env_thm, GSYM birs_auxTheory.birs_gen_env_NULL_thm]) ``bir_senv_GEN_list ^bprog_envtyl_tm``;

(* now try to instantiate *)
val _ = print "prepare generic SEQ thm\n";
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun ((fst o dest_eq o concl) bir_balrob_prog_def);
val bv_syp_gen = ``BVar "syp_gen" (BType_Imm Bit1)``;
val A_thm = CONV_RULE (RAND_CONV (LAND_CONV (REWRITE_CONV [birs_env_thm]))) symb_analysis_thm;
val B_thm = CONV_RULE (RAND_CONV (LAND_CONV (REWRITE_CONV [birs_env_thm]))) balrob_clzsi2_symb_merged_thm;
val _ = print "start instantiation\n";
(*
val cont_thm = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm bv_syp_gen A_thm B_thm;
val cont_thm_fixed = CONV_RULE (RAND_CONV (LAND_CONV (REWRITE_CONV [GSYM birs_env_thm]))) cont_thm;

Theorem balrob_insttest_symb_inst_thm = cont_thm_fixed
*)

val _ = export_theory ();


