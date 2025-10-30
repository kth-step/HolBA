open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open incr_spec_arm8Theory;

val _ = new_theory "incr_spec_bir";

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

Definition bspec_incr_pre_def:
 bspec_incr_pre (pre_x0:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))
End

Definition bspec_incr_post_def:
 bspec_incr_post (pre_x0:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x0)) (BExp_Const (Imm64 1w)))
End


(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem arm8_bmr_x0_equiv:
!b f b1 ms w.
 bmr_rel arm8_bmr (bir_state_t b (BEnv f) b1) ms ==>
 (f "R0" = SOME (BVal_Imm (Imm64 w)) <=> ms.REG 0w = w)
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  arm8_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem incr_arm8_pre_imp_bspec_pre_thm:
 bir_pre_arm8_to_bir (arm8_incr_pre pre_x0) (bspec_incr_pre pre_x0)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_incr_pre_def,bspec_incr_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   arm8_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,
   bir_envTheory.bir_env_lookup_def,
   bir_val_TF_bool2b_DEF
  ]
QED

Theorem incr_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8 (arm8_incr_post pre_x0) (\l. bspec_incr_post pre_x0) ls
Proof
 once_rewrite_tac [bir_post_bir_to_arm8_def,bspec_incr_post_def] >>
 once_rewrite_tac [bspec_incr_post_def] >>
 once_rewrite_tac [bspec_incr_post_def] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_eq
 ] >>

 rw [arm8_incr_post_def] >>

 METIS_TAC [arm8_bmr_x0_equiv]
QED

val _ = export_theory ();
