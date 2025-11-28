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

val _ = new_theory "isqrt_spec_bir";

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* before loop contract *)

Definition bspec_isqrt_pre_1_def:
 bspec_isqrt_pre_1 (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))
End

val bspec_isqrt_post_1_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 0w))``
];

Definition bspec_isqrt_post_1_def:
 bspec_isqrt_post_1 (pre_x10:word64) : bir_exp_t =
  ^bspec_isqrt_post_1_tm
End

(* loop body contract *)

val bspec_isqrt_pre_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))``
];

Definition bspec_isqrt_pre_2_def:
 bspec_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_pre_2_tm
End

val bspec_isqrt_post_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x14" (BType_Imm Bit64)))
     (BExp_BinExp
       BIExp_Mult
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w)))
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w))))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w)))``
];

Definition bspec_isqrt_post_2_def:
 bspec_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_post_2_tm
End

(* branch contract *)

val bspec_isqrt_pre_3_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``
];

Definition bspec_isqrt_pre_3_def:
 bspec_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
  ^bspec_isqrt_pre_3_tm
End

val bspec_isqrt_post_3_loop_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``,
  ``BExp_BinPred
     BIExp_LessOrEqual
      (BExp_Const (Imm64 pre_x14))
      (BExp_Const (Imm64 pre_x13))``
];

Definition bspec_isqrt_post_3_loop_def:
 bspec_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_loop_tm
End

val bspec_isqrt_post_3_ret_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``,
  ``BExp_BinPred
    BIExp_LessThan
    (BExp_Const (Imm64 pre_x13))
    (BExp_Const (Imm64 pre_x14))``
];

Definition bspec_isqrt_post_3_ret_def:
 bspec_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
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
   (\l. bspec_isqrt_post_1 pre_x10)
   ls
Proof
 fs [
  bir_post_bir_to_riscv_def,
  bspec_isqrt_post_1_def,
  GSYM bir_and_equiv
 ] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_eq
 ] >>

 rw [riscv_isqrt_post_1_def] >>

 METIS_TAC [
  riscv_bmr_x13_equiv,
  riscv_bmr_x15_equiv
 ]
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
   (\l. bspec_isqrt_post_2 pre_x13 pre_x15)
   ls
Proof
 fs [
  bir_post_bir_to_riscv_def,
  bspec_isqrt_post_2_def,
  GSYM bir_and_equiv
 ] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_eq
 ] >>

 rw [riscv_isqrt_post_2_def] >>

 METIS_TAC [
  riscv_bmr_x10_equiv,
  riscv_bmr_x13_equiv,
  riscv_bmr_x14_equiv,
  riscv_bmr_x15_equiv
 ]
QED

Theorem isqrt_riscv_pre_3_imp_bspec_pre_3_thm:
 bir_pre_riscv_to_bir
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14)
  (bspec_isqrt_pre_3 pre_x10 pre_x13 pre_x14)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_isqrt_pre_3_def,bspec_isqrt_pre_3_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem isqrt_riscv_post_3_imp_bspec_post_3_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14)
   (\l. if l = BL_Address (Imm64 0x10490w) then bspec_isqrt_post_3_loop pre_x10 pre_x13 pre_x14
     else if l = BL_Address (Imm64 0x104A0w) then bspec_isqrt_post_3_ret pre_x10 pre_x13 pre_x14
     else bir_exp_false)
   ls
Proof
 fs [bir_post_bir_to_riscv_def] >>
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>

 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 0x10490w)` >> fs [] >-
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
   `ms.c_PC ms.procID = 0x10490w` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >| [
      rw [riscv_isqrt_post_3_loop_def] >>
      METIS_TAC [
       riscv_bmr_x10_equiv,
       riscv_bmr_x13_equiv,
       riscv_bmr_x14_equiv,
       riscv_bmr_x15_equiv
      ],

     fs [isqrt_end_addr_3_loop_def],

     fs [isqrt_end_addr_3_loop_def]
   ]) >>
 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 0x104A0w)` >> fs [] >-
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
   `ms.c_PC ms.procID = 0x104A0w` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >| [
     fs [isqrt_end_addr_3_loop_def],
   
     fs [isqrt_end_addr_3_ret_def],

     rw [riscv_isqrt_post_3_ret_def] >>
     METIS_TAC [
      riscv_bmr_x10_equiv,
      riscv_bmr_x13_equiv,
      riscv_bmr_x14_equiv,
      riscv_bmr_x15_equiv
     ]
   ]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_exp_false_def,
  bir_val_false_def,
  bir_val_true_def
 ] >>
 rw []
QED

val _ = export_theory ();
