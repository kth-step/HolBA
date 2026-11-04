open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
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

open isqrt_spec_riscvTheory;

open bslSyntax;

val _ = new_theory "isqrt_spec_bir";

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* before loop contract *)

val bspec_isqrt_pre_1_tm =
  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10");

Definition bspec_isqrt_pre_1_def:
 bspec_isqrt_pre_1 (pre_x10:word64) : bir_exp_t =
  ^bspec_isqrt_pre_1_tm
End

val bspec_isqrt_post_1_tm = bandl [
  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x15"), bconst64 0)
];

Definition bspec_isqrt_post_1_def:
 bspec_isqrt_post_1 (pre_x10:word64) : bir_exp_t =
  ^bspec_isqrt_post_1_tm
End

(* loop body contract *)

val bspec_isqrt_pre_2_tm = bandl [
  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15")
];

Definition bspec_isqrt_pre_2_def:
 bspec_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_pre_2_tm
End

val bspec_isqrt_post_2_tm = bandl [
  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x15"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x14"),
   bmult (bplus (bconstvar64 "pre_x15", bconst64 1),
          bplus (bconstvar64 "pre_x15", bconst64 1))),

  beq (bden (bvarimm64 "x15"), bplus (bconstvar64 "pre_x15", bconst64 1))
];

Definition bspec_isqrt_post_2_def:
 bspec_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_post_2_tm
End

(* branch contract *)

val bspec_isqrt_pre_3_tm = bandl [
  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x14"), bconstvar64 "pre_x14"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15")
];

Definition bspec_isqrt_pre_3_def:
 bspec_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_pre_3_tm
End

val bspec_isqrt_post_3_loop_tm = bandl [
  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x14"), bconstvar64 "pre_x14"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15"),

  ble (bconstvar64 "pre_x14", bconstvar64 "pre_x13")
];

Definition bspec_isqrt_post_3_loop_def:
 bspec_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_loop_tm
End

val bspec_isqrt_post_3_ret_tm = bandl [
  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x14"), bconstvar64 "pre_x14"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15"),

  blt (bconstvar64 "pre_x13", bconstvar64 "pre_x14")
];

Definition bspec_isqrt_post_3_ret_def:
 bspec_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_ret_tm
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem isqrt_riscv_pre_1_imp_bspec_pre_1_thm:
 bir_pre_riscv_to_bir
  (riscv_isqrt_pre_1 pre_x10)
  (bspec_isqrt_pre_1 pre_x10)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_isqrt_pre_1_def,bspec_isqrt_pre_1_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

Theorem isqrt_riscv_post_1_imp_bspec_post_1_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_isqrt_post_1 pre_x10)
   (\l. if l = BL_Address (Imm64 isqrt_end_addr_1) then bspec_isqrt_post_1 pre_x10
        else bir_exp_false)
   ls
Proof
 rw [bir_post_bir_to_riscv_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 isqrt_end_addr_1)` >> fs [] >- (
  `ms.c_PC ms.procID = isqrt_end_addr_1` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
  fs [bspec_isqrt_post_1_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_envTheory.bir_env_read_def,
   bir_envTheory.bir_env_check_type_def,
   bir_envTheory.bir_env_lookup_type_def,
   bir_envTheory.bir_env_lookup_def,
   bir_eval_bin_pred_def,
   bir_eval_bin_pred_exists_64_eq
  ] >>
  rw [riscv_isqrt_post_1_def] >>
  METIS_TAC [riscv_bmr_x13_equiv, riscv_bmr_x15_equiv]
 ) >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def]
QED

Theorem isqrt_riscv_pre_2_imp_bspec_pre_2_thm:
 bir_pre_riscv_to_bir
  (riscv_isqrt_pre_2 pre_x13 pre_x15)
  (bspec_isqrt_pre_2 pre_x13 pre_x15)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_isqrt_pre_2_def,bspec_isqrt_pre_2_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem isqrt_riscv_post_2_imp_bspec_post_2_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_isqrt_post_2 pre_x13 pre_x15)
   (\l. if l = BL_Address (Imm64 isqrt_end_addr_2) then bspec_isqrt_post_2 pre_x13 pre_x15
        else bir_exp_false)
   ls
Proof
 rw [bir_post_bir_to_riscv_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 isqrt_end_addr_2)` >> fs [] >- (
  `ms.c_PC ms.procID = isqrt_end_addr_2` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
  fs [bspec_isqrt_post_2_def, GSYM bir_and_equiv] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_envTheory.bir_env_read_def,
   bir_envTheory.bir_env_check_type_def,
   bir_envTheory.bir_env_lookup_type_def,
   bir_envTheory.bir_env_lookup_def,
   bir_eval_bin_pred_def,
   bir_eval_bin_pred_exists_64_eq
  ] >>
  rw [riscv_isqrt_post_2_def] >>
  METIS_TAC [riscv_bmr_x10_equiv, riscv_bmr_x13_equiv, riscv_bmr_x14_equiv, riscv_bmr_x15_equiv]
 ) >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def]
QED

Theorem isqrt_riscv_pre_3_imp_bspec_pre_3_thm:
 bir_pre_riscv_to_bir
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15)
  (bspec_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_isqrt_pre_3_def,bspec_isqrt_pre_3_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem isqrt_riscv_post_3_imp_bspec_post_3_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14 pre_x15)
   (\l. if l = BL_Address (Imm64 isqrt_end_addr_3_loop) then bspec_isqrt_post_3_loop pre_x10 pre_x13 pre_x14 pre_x15
     else if l = BL_Address (Imm64 isqrt_end_addr_3_ret) then bspec_isqrt_post_3_ret pre_x10 pre_x13 pre_x14 pre_x15
     else bir_exp_false)
   ls
Proof
 fs [bir_post_bir_to_riscv_def] >>
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>

 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 isqrt_end_addr_3_loop)` >> fs [] >-
  (fs [bspec_isqrt_post_3_loop_def,GSYM bir_and_equiv] >>

   Cases_on `bs` >> Cases_on `b0` >>

   FULL_SIMP_TAC (std_ss++holBACore_ss) [
    bir_envTheory.bir_env_read_def,
    bir_envTheory.bir_env_check_type_def,
    bir_envTheory.bir_env_lookup_type_def,
    bir_envTheory.bir_env_lookup_def,
    bir_eval_bin_pred_def,
    bir_eval_bin_pred_exists_64_eq,
    bool2b_def,
    bool2w_def
   ] >>

   rw [bir_val_true_def,riscv_isqrt_post_3_def] >>
   `ms.c_PC ms.procID = isqrt_end_addr_3_loop` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
   fs [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def] >>
   rw [riscv_isqrt_post_3_loop_def] >>
   METIS_TAC [
    riscv_bmr_x10_equiv,
    riscv_bmr_x13_equiv,
    riscv_bmr_x14_equiv,
    riscv_bmr_x15_equiv
   ]) >>
 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 isqrt_end_addr_3_ret)` >> fs [] >-
  (fs [bspec_isqrt_post_3_ret_def,GSYM bir_and_equiv] >>

   Cases_on `bs` >> Cases_on `b0` >>

   FULL_SIMP_TAC (std_ss++holBACore_ss) [
    bir_envTheory.bir_env_read_def,
    bir_envTheory.bir_env_check_type_def,
    bir_envTheory.bir_env_lookup_type_def,
    bir_envTheory.bir_env_lookup_def,
    bir_eval_bin_pred_def,
    bir_eval_bin_pred_exists_64_eq,
    bool2b_def,
    bool2w_def
   ] >>

   rw [bir_val_true_def,riscv_isqrt_post_3_def] >>
   `ms.c_PC ms.procID = isqrt_end_addr_3_ret` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
   fs [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def] >>
   rw [riscv_isqrt_post_3_ret_def] >>
   METIS_TAC [
    riscv_bmr_x10_equiv,
    riscv_bmr_x13_equiv,
    riscv_bmr_x14_equiv,
    riscv_bmr_x15_equiv
   ]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_exp_false_def,
  bir_val_false_def,
  bir_val_true_def
 ] >>
 rw []
QED

val _ = export_theory ();
