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
open kernel_trap_spec_riscvTheory;
open kernel_trap_spec_birTheory;
open kernel_trap_return_symb_transfTheory;

val _ = new_theory "kernel_trap_return_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_kernel_trap_return_thm =
 get_riscv_contract_thm
  bspec_cont_kernel_trap_return
  kernel_trap_return_init_addr_def [kernel_trap_return_end_addr_def]
  bir_kernel_trap_progbin_def
  riscv_kernel_trap_return_pre_def riscv_kernel_trap_return_post_def
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
 ACCEPT_TAC riscv_cont_kernel_trap_return_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_kernel_trap_return;
Theorem riscv_cont_kernel_trap_return_full = GEN_ALL readable_thm;

val _ = export_theory ();
