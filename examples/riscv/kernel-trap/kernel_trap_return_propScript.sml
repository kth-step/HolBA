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
open kernel_trap_return_symb_transfTheory;

val _ = new_theory "kernel_trap_return_prop";

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem kernel_trap_return_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
  (bspec_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
Proof
 rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_return_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_extra_expsTheory.BExp_Aligned_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_immTheory.n2bs_def]) >>

 Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

 Cases_on `bs` >> Cases_on `b0` >>
  
 FULL_SIMP_TAC (std_ss) [riscv_kernel_trap_return_pre_def, bspec_kernel_trap_return_pre_def,bir_extra_expsTheory.BExp_Aligned_def] >>

 fs [GSYM bir_and_equiv] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def
 ] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 8w)) = SOME (Imm64 pre_mepc_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 16w)) = SOME (Imm64 pre_x1_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 24w)) = SOME (Imm64 pre_x2_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 32w)) = SOME (Imm64 pre_x3_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 40w)) = SOME (Imm64 pre_x4_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 48w)) = SOME (Imm64 pre_x5_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 56w)) = SOME (Imm64 pre_x6_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 64w)) = SOME (Imm64 pre_x7_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 72w)) = SOME (Imm64 pre_x8_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 80w)) = SOME (Imm64 pre_x9_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 88w)) = SOME (Imm64 pre_x10_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 96w)) = SOME (Imm64 pre_x11_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 104w)) = SOME (Imm64 pre_x12_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 112w)) = SOME (Imm64 pre_x13_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 120w)) = SOME (Imm64 pre_x14_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 128w)) = SOME (Imm64 pre_x15_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 136w)) = SOME (Imm64 pre_x16_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 144w)) = SOME (Imm64 pre_x17_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 152w)) = SOME (Imm64 pre_x18_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 160w)) = SOME (Imm64 pre_x19_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 168w)) = SOME (Imm64 pre_x20_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 176w)) = SOME (Imm64 pre_x21_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 184w)) = SOME (Imm64 pre_x22_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 192w)) = SOME (Imm64 pre_x23_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 200w)) = SOME (Imm64 pre_x24_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 208w)) = SOME (Imm64 pre_x25_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 216w)) = SOME (Imm64 pre_x26_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 224w)) = SOME (Imm64 pre_x27_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 232w)) = SOME (Imm64 pre_x28_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 240w)) = SOME (Imm64 pre_x29_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 248w)) = SOME (Imm64 pre_x30_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 256w)) = SOME (Imm64 pre_x31_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 rw [bir_eval_bin_pred_64_mem_eq] >>
 fs [riscv_mem_load_dword_bir_load_from_mem,bir_val_true_def]
QED

Theorem kernel_trap_return_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
   (\l. (bspec_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem))
   ls
Proof
 once_rewrite_tac [bir_post_bir_to_riscv_def,bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>

 fs [GSYM bir_and_equiv] >>

 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >>

 rw [bir_eval_bin_pred_exists_64_eq] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_kernel_trap_return_post_def,
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_kernel_trap_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_kernel_trap_return_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_kernel_trap_return_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_kernel_trap_return_thm =
 get_riscv_contract
  bspec_cont_kernel_trap_return
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_kernel_trap_prog_def
  [bspec_kernel_trap_return_pre_def]
  bspec_kernel_trap_return_pre_def kernel_trap_return_riscv_pre_imp_bspec_pre_thm
  [bspec_kernel_trap_return_post_def] kernel_trap_return_riscv_post_imp_bspec_post_thm
  bir_kernel_trap_riscv_lift_THM;

Theorem riscv_cont_kernel_trap_return:
 riscv_cont bir_kernel_trap_progbin kernel_trap_return_init_addr {kernel_trap_return_end_addr}
 (riscv_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
 (riscv_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
Proof
 rw [kernel_trap_return_init_addr_def,kernel_trap_return_end_addr_def] >>
 ACCEPT_TAC riscv_cont_kernel_trap_return_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_kernel_trap_return;
Theorem riscv_cont_kernel_trap_return_full = GEN_ALL readable_thm;

val _ = export_theory ();
