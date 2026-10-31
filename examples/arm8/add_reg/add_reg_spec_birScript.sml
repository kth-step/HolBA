open HolKernel boolLib Parse bossLib;

open markerTheory;

open holba_auxiliaryTheory;

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

open add_reg_spec_arm8Theory;

open bslSyntax;

val _ = new_theory "add_reg_spec_bir";

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

fun bregs_eq pre_x2 pre_x3 = [
  beq (bden (bvarimm 64 "R2"), bconst pre_x2),
  beq (bden (bvarimm 64 "R3"), bconst pre_x3)
];

(* before loop contract *)

val bspec_add_reg_pre_1_tm =
 bslSyntax.bandl (bregs_eq ``pre_x2:word64`` ``pre_x3:word64``);

Definition bspec_add_reg_pre_1_def:
 bspec_add_reg_pre_1 (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_pre_1_tm
End

Definition bspec_add_reg_post_1_def:
 bspec_add_reg_post_1 (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_pre_1_tm
End

(* loop branch contract *)

Definition bspec_add_reg_pre_2_def:
 bspec_add_reg_pre_2 (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_pre_1_tm
End

val bspec_add_reg_post_2_loop_tm = bslSyntax.bandl
 (bregs_eq ``pre_x2:word64`` ``pre_x3:word64`` @
  [bslt (bconst64 0, bconst ``pre_x2:word64``)]);

Definition bspec_add_reg_post_2_loop_def:
 bspec_add_reg_post_2_loop (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_post_2_loop_tm
End

val bspec_add_reg_post_2_ret_tm = bslSyntax.bandl
 (bregs_eq ``pre_x2:word64`` ``pre_x3:word64`` @
  [bsle (bconst ``pre_x2:word64``, bconst64 0)]);

Definition bspec_add_reg_post_2_ret_def:
 bspec_add_reg_post_2_ret (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_post_2_ret_tm
End

(* loop body contract *)

Definition bspec_add_reg_pre_3_def:
 bspec_add_reg_pre_3 (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_pre_1_tm
End

val bspec_add_reg_post_3_tm = bslSyntax.bandl [
  beq (bden (bvarimm 64 "R2"), bminus (bconst ``pre_x2:word64``, bconst64 1)),
  beq (bden (bvarimm 64 "R3"), bplus (bconst ``pre_x3:word64``, bconst64 1))
];

Definition bspec_add_reg_post_3_def:
 bspec_add_reg_post_3 (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_add_reg_post_3_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

val bspec_post_simps = [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_eq,
  bool2b_def,
  bool2w_def
];

Theorem add_reg_arm8_pre_1_imp_bspec_pre_1_thm:
 bir_pre_arm8_to_bir
  (arm8_add_reg_pre_1 pre_x2 pre_x3)
  (bspec_add_reg_pre_1 pre_x2 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_add_reg_pre_1_def,bspec_add_reg_pre_1_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem add_reg_arm8_post_1_imp_bspec_post_1_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_add_reg_post_1 pre_x2 pre_x3)
   (\l. if l = BL_Address (Imm64 0x38w) then bspec_add_reg_post_1 pre_x2 pre_x3
        else if l = BL_Address (Imm64 0x48w) then bir_exp_false
        else bir_exp_false)
   ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x38w)` >> fs [] >- (
  `ms.PC = 0x38w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  fs [bspec_add_reg_post_1_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) bspec_post_simps >>
  rw [arm8_add_reg_post_1_def, add_reg_end_addr_1_def] >>
  METIS_TAC [arm8_bmr_x2_equiv, arm8_bmr_x3_equiv]
 ) >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x48w)` >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def]
QED

Theorem add_reg_arm8_pre_2_imp_bspec_pre_2_thm:
 bir_pre_arm8_to_bir
  (arm8_add_reg_pre_2 pre_x2 pre_x3)
  (bspec_add_reg_pre_2 pre_x2 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_add_reg_pre_2_def,bspec_add_reg_pre_2_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem add_reg_arm8_post_2_imp_bspec_post_2_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_add_reg_post_2 pre_x2 pre_x3)
   (\l. if l = BL_Address (Imm64 0x20w) then bspec_add_reg_post_2_loop pre_x2 pre_x3
     else if l = BL_Address (Imm64 0x48w) then bspec_add_reg_post_2_ret pre_x2 pre_x3
     else bir_exp_false)
   ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x20w)` >> fs [] >- (
  `ms.PC = 0x20w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  fs [bspec_add_reg_post_2_loop_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) bspec_post_simps >>
  rw [arm8_add_reg_post_2_def, arm8_add_reg_post_2_loop_def,
      add_reg_end_addr_2_loop_def] >>
  fs [bir_val_true_def, if_bool_1w] >>
  METIS_TAC [arm8_bmr_x2_equiv, arm8_bmr_x3_equiv]
 ) >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x48w)` >> fs [] >- (
  `ms.PC = 0x48w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  fs [bspec_add_reg_post_2_ret_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) bspec_post_simps >>
  rw [arm8_add_reg_post_2_def, arm8_add_reg_post_2_ret_def,
      add_reg_end_addr_2_loop_def, add_reg_end_addr_2_ret_def] >>
  fs [bir_val_true_def, if_bool_1w] >>
  METIS_TAC [arm8_bmr_x2_equiv, arm8_bmr_x3_equiv]
 ) >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def]
QED

Theorem add_reg_arm8_pre_3_imp_bspec_pre_3_thm:
 bir_pre_arm8_to_bir
  (arm8_add_reg_pre_3 pre_x2 pre_x3)
  (bspec_add_reg_pre_3 pre_x2 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_add_reg_pre_3_def,bspec_add_reg_pre_3_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem add_reg_arm8_post_3_imp_bspec_post_3_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_add_reg_post_3 pre_x2 pre_x3)
   (\l. if l = BL_Address (Imm64 0x38w) then bspec_add_reg_post_3 pre_x2 pre_x3
        else if l = BL_Address (Imm64 0x48w) then bir_exp_false
        else bir_exp_false)
   ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x38w)` >> fs [] >- (
  `ms.PC = 0x38w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  fs [bspec_add_reg_post_3_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) bspec_post_simps >>
  `ms.REG 2w = pre_x2 - 1w /\ ms.REG 3w = pre_x3 + 1w`
   by METIS_TAC [arm8_bmr_x2_equiv, arm8_bmr_x3_equiv] >>
  rw [arm8_add_reg_post_3_def, add_reg_end_addr_3_def]
 ) >>
 Cases_on `b.bpc_label = BL_Address (Imm64 0x48w)` >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def]
QED

val _ = export_theory ();
