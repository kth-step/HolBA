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

open max_spec_arm8Theory;

open bslSyntax;

val _ = new_theory "max_spec_bir";

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_max_pre_tm = bandl [
  beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x0"),

  beq (bden (bvarimm64 "R1"), bconstvar64 "pre_x1")
];

Definition bspec_max_pre_def:
 bspec_max_pre (pre_x0:word64) (pre_x1:word64) : bir_exp_t =
  ^bspec_max_pre_tm
End

val bspec_max_post_tm = bandl [
  borl [
    beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x0"),

    beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x1")
  ],

  ble (bconstvar64 "pre_x0", bden (bvarimm64 "R0")),

  ble (bconstvar64 "pre_x1", bden (bvarimm64 "R0"))
];

Definition bspec_max_post_def:
 bspec_max_post (pre_x0:word64) (pre_x1:word64) : bir_exp_t =
  ^bspec_max_post_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem max_arm8_pre_imp_bspec_pre_thm:
 bir_pre_arm8_to_bir (arm8_max_pre pre_x0 pre_x1) (bspec_max_pre pre_x0 pre_x1)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_max_pre_def,bspec_max_pre_def] >-
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
  ] >>

  rw []
QED

Theorem max_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8 (arm8_max_post pre_x0 pre_x1) (\l. bspec_max_post pre_x0 pre_x1) ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >>
 `f "R0" = SOME (BVal_Imm (Imm64 (ms.REG 0w)))` by METIS_TAC [arm8_bmr_x0_equiv] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bspec_max_post_def,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_val_true_def,
  bool2b_def,
  bool2w_def
 ] >>
 rpt (pop_assum mp_tac) >> rw [arm8_max_post_def]
QED

val _ = export_theory ();
