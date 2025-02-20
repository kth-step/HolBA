open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

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

open logrootTheory arithmeticTheory pairTheory combinTheory;

val _ = new_theory "isqrt_spec";

Theorem riscv_bmr_lookup_x10[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x10" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 10w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x13[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x13" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 13w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x14[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x14" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 14w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x15[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x15" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 15w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_bpc_label_c_PC_BST_Running[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) BST_Running) ms /\
 b.bpc_label = BL_Address (Imm64 w) ==>
 ms.c_PC ms.procID = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_block_pc_def,
  bir_programcounter_t_component_equality
 ]
QED

(* ------ *)
(* Theory *)
(* ------ *)

Definition nSQRT_def:
 nSQRT (x:num) = ROOT 2 x
End

val arith_ss = srw_ss() ++ numSimps.old_ARITH_ss;

Theorem nSQRT_thm:
!(x:num) (p:num). nSQRT x =
      let 
        q = p * p
      in
      if (q <= x /\ x < q + 2 * p + 1) then p else nSQRT x
Proof
 RW_TAC (arith_ss ++ boolSimps.LET_ss) [nSQRT_def] >>
 MATCH_MP_TAC ROOT_UNIQUE >>
 RW_TAC bool_ss [ADD1,EXP_ADD,EXP_1,DECIDE ``2 = SUC 1``,
     LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
 fs []
QED

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x10488w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x104a0w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x10488w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x10490w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x10490w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x1049cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x1049cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x10490w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x104a0w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* general contract *)

Definition riscv_isqrt_pre_def:
 riscv_isqrt_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_isqrt_post_def:
 riscv_isqrt_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w (nSQRT (w2n pre_x10)))
End

(* before loop contract *)

Definition riscv_isqrt_pre_1_def:
 riscv_isqrt_pre_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_isqrt_post_1_def:
 riscv_isqrt_post_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x10 /\
   m.c_gpr m.procID 15w = 0w)
End

(* loop body contract *)

Definition riscv_isqrt_pre_2_def:
 riscv_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 15w = pre_x15)
End

Definition riscv_isqrt_post_2_def:
 riscv_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x15 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = (pre_x15 + 1w) * (pre_x15 + 1w) /\
   m.c_gpr m.procID 15w = pre_x15 + 1w)
End

(* loop branch contract *)

Definition riscv_isqrt_pre_3_def:
 riscv_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14)
End

Definition riscv_isqrt_post_3_loop_def:
 riscv_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x14 <=+ pre_x13)
End

Definition riscv_isqrt_post_3_ret_def:
 riscv_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x13 <+ pre_x14)
End

Definition riscv_isqrt_post_3_def:
 riscv_isqrt_post_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  if m.c_PC m.procID = isqrt_end_addr_3_loop then
    riscv_isqrt_post_3_loop pre_x10 pre_x13 pre_x14 m
  else if m.c_PC m.procID = isqrt_end_addr_3_ret then
    riscv_isqrt_post_3_ret pre_x10 pre_x13 pre_x14 m
  else F
End

(* --------------- *)
(* HL BIR contract *)
(* --------------- *)

Definition bir_isqrt_pre_def:
 bir_isqrt_pre (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bir_isqrt_post_def:
 bir_isqrt_post (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w (nSQRT (w2n x)))))
End

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
  riscv_bmr_lookup_x13,
  riscv_bmr_lookup_x15
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
  riscv_bmr_lookup_x10,
  riscv_bmr_lookup_x13,
  riscv_bmr_lookup_x14,
  riscv_bmr_lookup_x15
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
   `ms.c_PC ms.procID = 0x10490w` by METIS_TAC [riscv_bmr_bpc_label_c_PC_BST_Running] >| [
      rw [riscv_isqrt_post_3_loop_def] >>
      METIS_TAC [
       riscv_bmr_lookup_x10,
       riscv_bmr_lookup_x13,
       riscv_bmr_lookup_x14,
       riscv_bmr_lookup_x15
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
   `ms.c_PC ms.procID = 0x104A0w` by METIS_TAC [riscv_bmr_bpc_label_c_PC_BST_Running] >| [
     fs [isqrt_end_addr_3_loop_def],
   
     fs [isqrt_end_addr_3_ret_def],

     rw [riscv_isqrt_post_3_ret_def] >>
     METIS_TAC [
      riscv_bmr_lookup_x10,
      riscv_bmr_lookup_x13,
      riscv_bmr_lookup_x14,
      riscv_bmr_lookup_x15
     ]
   ]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_false_def,bir_val_false_def,bir_val_true_def] >>
 rw []
QED

val _ = export_theory ();
