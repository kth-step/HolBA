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
(* commonBalrobScriptLib.sml *)
val countw_space_req = 21;
val bspec_balrob_clzsi2_pre_tm =
  ``BExp_BinPred BIExp_LessOrEqual
       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
       (BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(0x10000000 - countw_space_req, 64))))``;

Definition bspec_balrob_clzsi2_pre_def:
  bspec_balrob_clzsi2_pre : bir_exp_t =
   ^bspec_balrob_clzsi2_pre_tm
End

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_balrob_prog_def
  balrob_clzsi2_init_addr_def [balrob_clzsi2_end_addr_def]
  bspec_balrob_clzsi2_pre_def balrob_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem aes_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem aes_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
