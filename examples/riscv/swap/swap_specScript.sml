open HolKernel boolLib Parse bossLib;

open markerTheory;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open tutorial_smtSupportLib;
open bir_symbLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open distribute_generic_stuffTheory;

open swapTheory;

val _ = new_theory "swap_spec";

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_swap_pre_def:
 riscv_swap_pre x y xv yv (m : riscv_state) =
  (^(mem_addrs_aligned_prog_disj_riscv_tm ``x:word64``) /\
   m.c_gpr m.procID 10w = x /\
   riscv_mem_load_dword m.MEM8 x = xv /\
   ^(mem_addrs_aligned_prog_disj_riscv_tm ``y:word64``) /\
   m.c_gpr m.procID 11w = y /\
   riscv_mem_load_dword m.MEM8 y = yv)
End

Definition riscv_swap_post_def:
 riscv_swap_post x y xv yv (m : riscv_state) =
  (riscv_mem_load_dword m.MEM8 x = yv /\
   riscv_mem_load_dword m.MEM8 y = xv)
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_swap_pre_tm = bslSyntax.bandl [
 mem_addrs_aligned_prog_disj_tm "x10",
 mem_addrs_aligned_prog_disj_tm "x11",
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))``,
 ``BExp_BinPred
      BIExp_Equal
      (BExp_Load
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "x10" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 xv))``,
 ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x11" (BType_Imm Bit64)))
     (BExp_Const (Imm64 y))``,
 ``BExp_BinPred
    BIExp_Equal
     (BExp_Load
      (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x11" (BType_Imm Bit64)))
      BEnd_LittleEndian Bit64)
     (BExp_Const (Imm64 yv))`` 
];

Definition bspec_swap_pre_def:
  bspec_swap_pre x y xv yv : bir_exp_t =
   ^bspec_swap_pre_tm
End

val bspec_swap_post_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 x))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 yv))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 y))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 xv))``
];

Definition bspec_swap_post_def:
 bspec_swap_post x y xv yv : bir_exp_t = 
  ^bspec_swap_post_tm
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem swap_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
  (bspec_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
Proof
  rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_swap_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_extra_expsTheory.BExp_Aligned_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_immTheory.n2bs_def]) >>
  FULL_SIMP_TAC (std_ss) [riscv_swap_pre_def, bspec_swap_pre_def, riscv_mem_load_dword_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_extra_expsTheory.BExp_Aligned_def, pred_setTheory.INSERT_UNION_EQ] >>
  FULL_SIMP_TAC (std_ss) [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  PAT_X_ASSUM ``bmr_rel riscv_bmr A B`` (fn t => REWRITE_TAC [REWRITE_RULE [riscv_bmr_rel_EVAL] t] >> ASSUME_TAC t) >>
  `(?mem_n.
        bir_env_read (BVar "MEM8" (BType_Mem Bit64 Bit8)) bs.bst_environ =
        SOME (BVal_Mem Bit64 Bit8 mem_n) /\
        ms.MEM8 = (\a. n2w (bir_load_mmap mem_n (w2n a))) /\
        bir_env_var_is_declared bs.bst_environ (BVar "tmp_MEM8" (BType_Mem Bit64 Bit8)))`
    by METIS_TAC [riscv_bmr_rel_EVAL] >>
  ASM_SIMP_TAC (std_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_immTheory.bool2b_def, bir_immTheory.bool2w_def] >>
  `bir_eval_bin_pred BIExp_Equal
                      (bir_eval_load (SOME (BVal_Mem Bit64 Bit8 mem_n))
                         (SOME (BVal_Imm (Imm64 pre_x10))) BEnd_LittleEndian
                         Bit64) (SOME (BVal_Imm (Imm64 pre_x10_mem_deref))) = SOME (BVal_Imm (Imm1 1w))` by (
    fs [type_of_bir_val_def,bir_eval_load_BASIC_REWR,type_of_bir_imm_def] >>
    Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (b2n (Imm64 pre_x10))` >-
     (fs [bir_exp_memTheory.bir_load_from_mem_REWRS]) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
    (**)
    fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
    POP_ASSUM (fn t => REWRITE_TAC [GSYM t]) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    (**)
    REPEAT (PAT_X_ASSUM ``B1 @@ B2 @@ B3 @@ B4 @@ B5 @@ B6 @@ B7 @@ B8 = A`` (ASSUME_TAC o GSYM)) >>
    ASM_REWRITE_TAC [] >>
    SIMP_TAC std_ss [bir_exp_memTheory.bir_mem_addr_w2n_SIZES, bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES]) >>
  `bir_eval_bin_pred BIExp_Equal
   (bir_eval_load (SOME (BVal_Mem Bit64 Bit8 mem_n))
                  (SOME (BVal_Imm (Imm64 pre_x11)))
                  BEnd_LittleEndian Bit64)
   (SOME (BVal_Imm (Imm64 pre_x11_mem_deref))) = SOME (BVal_Imm (Imm1 1w))` by (
    fs [type_of_bir_val_def,bir_eval_load_BASIC_REWR,type_of_bir_imm_def] >>
    Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (b2n (Imm64 pre_x11))` >-
     (fs [bir_exp_memTheory.bir_load_from_mem_REWRS]) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
    (**)
    fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
    POP_ASSUM (fn t => REWRITE_TAC [GSYM t]) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    (**)
    REPEAT (PAT_X_ASSUM ``B1 @@ B2 @@ B3 @@ B4 @@ B5 @@ B6 @@ B7 @@ B8 = A`` (ASSUME_TAC o GSYM)) >>
    ASM_REWRITE_TAC [] >>
    SIMP_TAC std_ss [bir_exp_memTheory.bir_mem_addr_w2n_SIZES, bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES]) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_val_true_def]
QED

Theorem swap_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
   (\l. (bspec_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref))
   ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_swap_post_def,bspec_swap_post_def,riscv_mem_load_dword_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Q.ABBREV_TAC `g = ?z. f "MEM8" = SOME z /\ BType_Mem Bit64 Bit8 = type_of_bir_val z` >>
 Cases_on `g` >> fs [Abbrev_def] >| [
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   Cases_on `z` >> fs [type_of_bir_val_def,bir_eval_load_BASIC_REWR,type_of_bir_imm_def] >>
   Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 f' BEnd_LittleEndian (b2n (Imm64 pre_x10))` >>
   Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 f' BEnd_LittleEndian (b2n (Imm64 pre_x11))` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_REWRS] >>
   Cases_on `x` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>
   Cases_on `x'` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>
   fs [bool2w_def,bir_val_true_def] >>
   Cases_on `c = pre_x11_mem_deref` >>
   Cases_on `c' = pre_x10_mem_deref` >>
   fs [] >>
   rw [] >>
   fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
   fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
   `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
   fs [bir_exp_memTheory.bir_mem_addr_w2n] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def],

   FULL_SIMP_TAC (std_ss++holBACore_ss) [],

   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   Cases_on `z` >> fs [type_of_bir_val_def,bir_eval_load_BASIC_REWR,type_of_bir_imm_def] >>
   Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 f' BEnd_LittleEndian (b2n (Imm64 pre_x10))` >>
   Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 f' BEnd_LittleEndian (b2n (Imm64 pre_x11))` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_REWRS] >>
   Cases_on `x` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>
   Cases_on `x'` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>
   fs [bool2w_def,bir_val_true_def] >>
   Cases_on `c = pre_x11_mem_deref` >>
   Cases_on `c' = pre_x10_mem_deref` >>
   fs [] >>
   rw [] >>
   fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
   fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
   `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
   fs [bir_exp_memTheory.bir_mem_addr_w2n] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def],

   FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ]
QED

val _ = export_theory ();
