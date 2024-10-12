open HolKernel Parse boolLib bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_predLib;

open bir_symbLib;

open balrobLib;

val _ = new_theory "balrob_ends";

(* __clzsi2 *)

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition balrob_clzsi2_init_addr_def:
 balrob_clzsi2_init_addr : word32 = 0x100013b4w
End

Definition balrob_clzsi2_end_addr_def:
 balrob_clzsi2_end_addr : word32 = 0x100013dcw
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)
val bir_countw_hvar_tm = ``BExp_Const (Imm64 pre_countw)``;
val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
fun mk_countw_const v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
fun mk_countw_plus tm v = bslSyntax.bplus (tm, mk_countw_const v);

(* commonBalrobScriptLib.sml *)
val countw_space_req = 21;
val symbexec_init_tm = (* TODO: need SP here too *)
  ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_const (0x10000000 - countw_space_req))``;

Definition bspec_balrob_clzsi2_init_def:
  bspec_balrob_clzsi2_init : bir_exp_t =
   ^symbexec_init_tm
End

val bspec_balrob_clzsi2_pre_tm = bslSyntax.bandl [
  bslSyntax.beq (bir_countw_bvar_tm, bir_countw_hvar_tm),
  symbexec_init_tm
];

Definition bspec_balrob_clzsi2_pre_def:
  bspec_balrob_clzsi2_pre (pre_countw:word64) : bir_exp_t =
   ^bspec_balrob_clzsi2_pre_tm
End

(* TODO: move this after the symbolic execution and infer the minimum and the maximum *)
(* TODO: make this an interval statement *)
val (countw_min, countw_max) = (21, 21);
val bspec_balrob_clzsi2_post_tm = bslSyntax.bandl [
 ``BExp_BinPred BIExp_LessOrEqual
       ^(mk_countw_plus bir_countw_hvar_tm countw_min)
       ^(bir_countw_bvar_tm)``,
 ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_plus bir_countw_hvar_tm countw_max)``
];

Definition bspec_balrob_clzsi2_post_def:
 bspec_balrob_clzsi2_post (pre_countw:word64) : bir_exp_t =
  ^bspec_balrob_clzsi2_post_tm
End

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val pcond_symb_o = SOME ``BVar "syp_gen" (BType_Imm Bit1)``;
val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm_gen
  pcond_symb_o
  bir_balrob_prog_def
  balrob_clzsi2_init_addr_def [balrob_clzsi2_end_addr_def]
  bspec_balrob_clzsi2_init_def balrob_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem balrob_clzsi2_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem balrob_clzsi2_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
