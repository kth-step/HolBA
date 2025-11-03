open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;

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

open swap_spec_arm8Theory;

val _ = new_theory "swap_spec_bir";

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_swap_pre_tm = bslSyntax.bandl [
 mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "R0",
 mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "R1",
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))``,
 ``BExp_BinPred
      BIExp_Equal
      (BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 pre_x0_deref))``,
 ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "R1" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x1))``,
 ``BExp_BinPred
    BIExp_Equal
     (BExp_Load
      (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "R1" (BType_Imm Bit64)))
      BEnd_LittleEndian Bit64)
     (BExp_Const (Imm64 pre_x1_deref))`` 
];

Definition bspec_swap_pre_def:
 bspec_swap_pre (pre_x0:word64) (pre_x1:word64)
  (pre_x0_deref:word64) (pre_x1_deref:word64) : bir_exp_t =
   ^bspec_swap_pre_tm
End

val bspec_swap_post_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 pre_x0))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x1_deref))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 pre_x1))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x0_deref))``
];

Definition bspec_swap_post_def:
 bspec_swap_post (pre_x0:word64) (pre_x1:word64)
  (pre_x0_deref:word64) (pre_x1_deref:word64) : bir_exp_t =
  ^bspec_swap_post_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem bir_load_from_mem_arm8_load_64:
 !ms map (w_ref:word64) w_deref.
  ms.MEM = (\a. n2w (bir_load_mmap map (w2n a))) /\
  bir_load_from_mem Bit8 Bit64 Bit64 map BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref) ==>
  arm8_load_64 ms.MEM w_ref = w_deref
Proof
 rw [arm8_load_64_def] >>
 fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
 `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n]
QED

Theorem arm8_load_64_bir_load_from_mem:
 !ms map (w_ref:word64) w_deref.
 arm8_load_64 ms.MEM w_ref = w_deref /\
 ms.MEM = (\a. n2w (bir_load_mmap map (w2n a))) ==>
 bir_load_from_mem Bit8 Bit64 Bit64 map BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref)
Proof
 rw [arm8_load_64_def] >>
 fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
 `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n]
QED

Theorem bmr_rel_arm8_MEM_map:
 !b f b1 ms map.
 bmr_rel arm8_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "MEM" = SOME (BVal_Mem Bit64 Bit8 map) ==>
 ms.MEM = (\a. n2w (bir_load_mmap map (w2n a)))
Proof
 rw [
  arm8_bmr_rel_EVAL,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_envTheory.bir_var_name_def
 ] >>
 fs []
QED

(* ----- *)

Theorem swap_arm8_pre_imp_bspec_pre_thm:
 bir_pre_arm8_to_bir
  (arm8_swap_pre pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
  (bspec_swap_pre pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
Proof
 rw [bir_pre_arm8_to_bir_def] >-
   (rw [bspec_swap_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [
     bir_extra_expsTheory.BExp_Aligned_def,
     bir_immTheory.n2bs_def]) >>
  Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

  Cases_on `bs` >> Cases_on `b0` >>
  
  FULL_SIMP_TAC (std_ss) [
   arm8_swap_pre_def,
   bspec_swap_pre_def,
   bir_extra_expsTheory.BExp_Aligned_def
  ] >>

  fs [GSYM bir_and_equiv] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   arm8_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def
  ] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n pre_x0) = SOME (Imm64 pre_x0_deref)`
  by METIS_TAC [arm8_load_64_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n pre_x1) = SOME (Imm64 pre_x1_deref)`
  by METIS_TAC [arm8_load_64_bir_load_from_mem] >>

 rw [bir_eval_bin_pred_64_mem_eq] >>
 fs [arm8_load_64_bir_load_from_mem,bir_val_true_def]
QED

Theorem swap_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8
   (arm8_swap_post pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
   (\l. (bspec_swap_post pre_x0 pre_x1 pre_x0_deref pre_x1_deref))
   ls
Proof
 fs [
  bir_post_bir_to_arm8_def,
  bspec_swap_post_def,
  GSYM bir_and_equiv
 ] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_mem_eq
 ] >>

 rw [arm8_swap_post_def] >>

 METIS_TAC [
  bir_load_from_mem_arm8_load_64,
  bmr_rel_arm8_MEM_map
 ]
QED

val _ = export_theory ();
