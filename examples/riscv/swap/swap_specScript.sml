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

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_dword (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_dword (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_swap_pre_def:
 riscv_swap_pre x y xv yv (m : riscv_state) =
  (m.c_gpr m.procID 10w = x /\
   riscv_mem_load_dword m.MEM8 x = xv /\
   m.c_gpr m.procID 11w = y /\
   riscv_mem_load_dword m.MEM8 y = yv)
End

Definition riscv_swap_post_def:
 riscv_swap_post x y xv yv (m : riscv_state) =
  (riscv_mem_load_dword m.MEM8 x = yv /\
   riscv_mem_load_dword m.MEM8 y = xv)
End

val bir_swap_pre_tm = bslSyntax.bandl [
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

Definition bir_swap_pre_def:
  bir_swap_pre x y xv yv : bir_exp_t =
   ^bir_swap_pre_tm
End

Definition bir_swap_post_def:
 bir_swap_post x y xv yv : bir_exp_t = 
  BExp_BinExp BIExp_And
   (BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 x))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 yv)))
   (BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 y))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 xv)))
End

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem swap_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
  (bir_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
Proof
 cheat
QED

Theorem swap_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
   (\l. (bir_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref))
   ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_swap_post_def,bir_swap_post_def,riscv_mem_load_dword_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Q.ABBREV_TAC `g = ?z. f "MEM8" = SOME z /\ BType_Mem Bit64 Bit8 = type_of_bir_val z` >>
 Cases_on `g` >> fs [Abbrev_def] >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
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
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def]) >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) []) >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
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
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def]) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

val _ = export_theory ();
