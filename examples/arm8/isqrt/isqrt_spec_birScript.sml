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

open isqrt_spec_arm8Theory;

val _ = new_theory "isqrt_spec_bir";

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* before loop contract *)

Definition bspec_isqrt_pre_1_def:
 bspec_isqrt_pre_1 (pre_x0:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))
End

val bspec_isqrt_post_1_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 0w))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))``
];

Definition bspec_isqrt_post_1_def:
 bspec_isqrt_post_1 (pre_x0:word64) : bir_exp_t =
  ^bspec_isqrt_post_1_tm
End

(* loop body contract *)

val bspec_isqrt_pre_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``
];

Definition bspec_isqrt_pre_2_def:
 bspec_isqrt_pre_2 (pre_x1:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_isqrt_pre_2_tm
End

val bspec_isqrt_post_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x1)) (BExp_Const (Imm64 1w)))``,
  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "R2" (BType_Imm Bit64)))
     (BExp_BinExp
       BIExp_Mult
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x1)) (BExp_Const (Imm64 1w)))
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x1)) (BExp_Const (Imm64 1w))))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``
];

Definition bspec_isqrt_post_2_def:
 bspec_isqrt_post_2 (pre_x1:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_isqrt_post_2_tm
End

(* branch contract *)

val bspec_isqrt_pre_3_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x2))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``
];

Definition bspec_isqrt_pre_3_def:
 bspec_isqrt_pre_3 (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_isqrt_pre_3_tm
End

val bspec_isqrt_post_3_loop_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x2))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``,
  ``BExp_BinPred
     BIExp_LessOrEqual
      (BExp_Const (Imm64 pre_x2))
      (BExp_Const (Imm64 pre_x3))``
];

Definition bspec_isqrt_post_3_loop_def:
 bspec_isqrt_post_3_loop (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_loop_tm
End

val bspec_isqrt_post_3_ret_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x2))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``,
  ``BExp_BinPred
    BIExp_LessThan
    (BExp_Const (Imm64 pre_x3))
    (BExp_Const (Imm64 pre_x2))``
];

Definition bspec_isqrt_post_3_ret_def:
 bspec_isqrt_post_3_ret (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_ret_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem isqrt_arm8_pre_1_imp_bspec_pre_1_thm:
 bir_pre_arm8_to_bir
  (arm8_isqrt_pre_1 pre_x0)
  (bspec_isqrt_pre_1 pre_x0)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_isqrt_pre_1_def,bspec_isqrt_pre_1_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

Theorem isqrt_arm8_post_1_imp_bspec_post_1_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_isqrt_post_1 pre_x0)
   (\l. bspec_isqrt_post_1 pre_x0)
   ls
Proof
 fs [
  bir_post_bir_to_arm8_def,
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

 rw [arm8_isqrt_post_1_def] >>

 METIS_TAC [
  arm8_bmr_x1_equiv,
  arm8_bmr_x3_equiv
 ]
QED

Theorem isqrt_arm8_pre_2_imp_bspec_pre_2_thm:
 bir_pre_arm8_to_bir
  (arm8_isqrt_pre_2 pre_x1 pre_x3)
  (bspec_isqrt_pre_2 pre_x1 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_isqrt_pre_2_def,bspec_isqrt_pre_2_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem isqrt_arm8_post_2_imp_bspec_post_2_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_isqrt_post_2 pre_x1 pre_x3)
   (\l. bspec_isqrt_post_2 pre_x1 pre_x3)
   ls
Proof
 fs [
  bir_post_bir_to_arm8_def,
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

 rw [arm8_isqrt_post_2_def] >>

 METIS_TAC [
  arm8_bmr_x0_equiv,
  arm8_bmr_x1_equiv,
  arm8_bmr_x2_equiv,
  arm8_bmr_x3_equiv
 ]
QED

Theorem isqrt_arm8_pre_3_imp_bspec_pre_3_thm:
 bir_pre_arm8_to_bir
  (arm8_isqrt_pre_3 pre_x1 pre_x2 pre_x3)
  (bspec_isqrt_pre_3 pre_x1 pre_x2 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_isqrt_pre_3_def,bspec_isqrt_pre_3_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bool2b_def,bool2w_def] >>
 rw []
QED

Theorem isqrt_arm8_post_3_imp_bspec_post_3_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_isqrt_post_3 pre_x1 pre_x2 pre_x3)
   (\l. if l = BL_Address (Imm64 0x720w) then bspec_isqrt_post_3_loop pre_x1 pre_x2 pre_x3
     else if l = BL_Address (Imm64 0x734w) then bspec_isqrt_post_3_ret pre_x1 pre_x2 pre_x3
     else bir_exp_false)
   ls
Proof
 fs [bir_post_bir_to_arm8_def] >>
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>

 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 0x720w)` >> fs [] >-
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
   
   rw [bir_val_true_def,arm8_isqrt_post_3_def] >>
   `ms.PC = 0x720w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >| [
      rw [arm8_isqrt_post_3_loop_def] >>
      METIS_TAC [
       arm8_bmr_x0_equiv,
       arm8_bmr_x1_equiv,
       arm8_bmr_x2_equiv,
       arm8_bmr_x3_equiv
      ],

     fs [isqrt_end_addr_3_loop_def],

     fs [isqrt_end_addr_3_loop_def]
   ]) >>
 Cases_on `bs.bst_pc.bpc_label = BL_Address (Imm64 0x734w)` >> fs [] >-
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
   
   rw [bir_val_true_def,arm8_isqrt_post_3_def] >>
   `ms.PC = 0x734w` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >| [
     fs [isqrt_end_addr_3_loop_def],
   
     fs [isqrt_end_addr_3_ret_def],

     rw [arm8_isqrt_post_3_ret_def] >>
     METIS_TAC [
      arm8_bmr_x0_equiv,
      arm8_bmr_x1_equiv,
      arm8_bmr_x2_equiv,
      arm8_bmr_x3_equiv
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
