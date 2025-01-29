open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_interval_expTheory;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open HolBACoreSimps;
open bir_extra_expsTheory;

open kernel_trapTheory;
open kernel_trap_specTheory;
open kernel_trap_entry_symb_transfTheory;

val _ = new_theory "kernel_trap_entry_prop";

Theorem bir_eval_bin_pred_eq[local]:
 !f w.
 (bir_eval_bin_pred BIExp_Equal
  (if (?z. f reg = SOME z ∧ BType_Imm Bit64 = type_of_bir_val z)
  then f reg else NONE) (SOME (BVal_Imm (Imm64 w))) = SOME bir_val_true) <=>
 (f reg = SOME (BVal_Imm (Imm64 w)))
Proof
 REPEAT STRIP_TAC >>
 Q.ABBREV_TAC `g = ?z. f reg = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 fs [Abbrev_def] >-
  (Cases_on `z` >> fs [type_of_bir_val_def] >>
   Cases_on `b` >> fs [type_of_bir_imm_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def,bool2w_def] >>
   Cases_on `c = w` >> fs [bir_val_true_def]) >>
 STRIP_TAC >>
 fs [type_of_bir_val_def,type_of_bir_imm_def]
QED

Theorem bir_eval_bin_pred_mem_eq[local]:
 !f mm w_ref w_deref.
 (bir_eval_bin_pred BIExp_Equal
  (bir_eval_load
   (if (?z. f mm = SOME z /\ BType_Mem Bit64 Bit8 = type_of_bir_val z)
    then f mm else NONE) (SOME (BVal_Imm (Imm64 w_ref))) BEnd_LittleEndian Bit64)
 (SOME (BVal_Imm (Imm64 w_deref))) = SOME bir_val_true) 
   <=>
 (?map. f mm = SOME (BVal_Mem Bit64 Bit8 map) /\
  bir_load_from_mem Bit8 Bit64 Bit64 map BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref))
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 Q.ABBREV_TAC `g = ?z. f mm = SOME z /\ BType_Mem Bit64 Bit8 = type_of_bir_val z` >>
 Cases_on `g` >> fs [Abbrev_def] >-
  (Cases_on `z` >> fs [type_of_bir_val_def,bir_eval_load_BASIC_REWR,type_of_bir_imm_def] >>
   Cases_on `bir_load_from_mem Bit8 Bit64 Bit64 f' BEnd_LittleEndian (b2n (Imm64 w_ref))` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_REWRS] >>
   Cases_on `x` >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def,bool2w_def] >>
   Cases_on `c = w_deref` >>
   fs [bir_val_true_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 METIS_TAC [type_of_bir_val_def]
QED

Theorem bir_load_from_mem_riscv_load_dword[local]:
!b f b1 ms map w_ref w_deref.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "MEM8" = SOME (BVal_Mem Bit64 Bit8 map) /\
 bir_load_from_mem Bit8 Bit64 Bit64 map BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref) ==>
 riscv_mem_load_dword ms.MEM8 w_ref = w_deref
Proof
 rw [riscv_mem_load_dword_def] >>
 fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
 `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def
 ]
QED

Theorem riscv_bmr_lookup_mscratch[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "mscratch" = SOME (BVal_Imm (Imm64 w)) ==>
 (ms.c_MCSR ms.procID).mscratch = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x1[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x1" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 1w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x2[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x2" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 2w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x3[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x3" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 3w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x4[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x4" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 4w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x5[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x5" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 5w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x6[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x6" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 6w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x7[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x7" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 7w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x8[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x8" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 8w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x9[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x9" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 9w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

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

Theorem riscv_bmr_lookup_x11[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x11" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 11w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x12[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x12" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 12w = w
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

Theorem riscv_bmr_lookup_x16[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x16" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 16w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x17[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x17" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 17w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x18[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x18" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 18w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

Theorem riscv_bmr_lookup_x19[local]:
!b f b1 ms w.
 bmr_rel riscv_bmr (bir_state_t b (BEnv f) b1) ms /\
 f "x19" = SOME (BVal_Imm (Imm64 w)) ==>
 ms.c_gpr ms.procID 19w = w
Proof
 rw [] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem kernel_trap_entry_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
  (bspec_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
Proof
  rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_entry_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_extra_expsTheory.BExp_Aligned_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_immTheory.n2bs_def,BExp_unchanged_mem_interval_distinct_def]) >>

  Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

  Cases_on `bs` >> Cases_on `b0` >>
  
  FULL_SIMP_TAC (std_ss) [riscv_kernel_trap_entry_pre_def, bspec_kernel_trap_entry_pre_def,bir_extra_expsTheory.BExp_Aligned_def] >>
  
  fs [GSYM bir_and_equiv] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def,
   BExp_unchanged_mem_interval_distinct_def
 ] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,bir_immTheory.bool2b_def,bir_immTheory.bool2w_def] >>

 rw []
QED

Theorem kernel_trap_entry_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
   (\l. (bspec_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31))
   ls
Proof
 fs [bir_post_bir_to_riscv_def,bspec_kernel_trap_entry_post_def,GSYM bir_and_equiv] >>

 Cases_on `bs` >>
 Cases_on `b0` >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_mem_eq,
  bir_eval_bin_pred_eq
 ] >>

 rw [riscv_kernel_trap_entry_post_def] >>

 METIS_TAC [
  bir_load_from_mem_riscv_load_dword,
  riscv_bmr_lookup_mscratch,
  riscv_bmr_lookup_x2,
  riscv_bmr_lookup_x3,
  riscv_bmr_lookup_x10,
  riscv_bmr_lookup_x11,
  riscv_bmr_lookup_x12
 ]
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_kernel_trap_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_kernel_trap_entry_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_kernel_trap_entry_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_kernel_trap_entry_thm =
 get_riscv_contract
  bspec_cont_kernel_trap_entry
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_kernel_trap_prog_def
  [bspec_kernel_trap_entry_pre_def]
  bspec_kernel_trap_entry_pre_def kernel_trap_entry_riscv_pre_imp_bspec_pre_thm
  [bspec_kernel_trap_entry_post_def] kernel_trap_entry_riscv_post_imp_bspec_post_thm
  bir_kernel_trap_riscv_lift_THM;

Theorem riscv_cont_kernel_trap_entry:
 riscv_cont bir_kernel_trap_progbin kernel_trap_entry_init_addr {kernel_trap_entry_end_addr}
 (riscv_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause pre_mhartid
      pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6 pre_x7 pre_x8
      pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14 pre_x15 pre_x16 pre_x17
      pre_x18 pre_x19 pre_x20 pre_x21 pre_x22 pre_x23 pre_x24 pre_x25 pre_x26
      pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
 (riscv_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause pre_mhartid
      pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6 pre_x7 pre_x8
      pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14 pre_x15 pre_x16 pre_x17
      pre_x18 pre_x19 pre_x20 pre_x21 pre_x22 pre_x23 pre_x24 pre_x25 pre_x26
      pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
Proof
 rw [kernel_trap_entry_init_addr_def,kernel_trap_entry_end_addr_def] >>
 ACCEPT_TAC riscv_cont_kernel_trap_entry_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_kernel_trap_entry;
Theorem riscv_cont_kernel_trap_entry_full = GEN_ALL readable_thm;

val _ = export_theory ();
