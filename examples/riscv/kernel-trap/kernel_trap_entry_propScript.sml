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
open kernel_trap_spec_riscvTheory;
open kernel_trap_spec_birTheory;
open kernel_trap_entry_symb_transfTheory;

val _ = new_theory "kernel_trap_entry_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_kernel_trap_entry_thm =
 get_riscv_contract_thm
  bir_cont_kernel_trap_entry
  kernel_trap_entry_init_addr_def [kernel_trap_entry_end_addr_def]
  bir_kernel_trap_progbin_def
  riscv_kernel_trap_entry_pre_def riscv_kernel_trap_entry_post_def
  bir_kernel_trap_prog_def
  [riscv_kernel_trap_entry_pre_bir_def]
  riscv_kernel_trap_entry_pre_bir_def riscv_kernel_trap_entry_pre_to_bir_thm
  [riscv_kernel_trap_entry_post_bir_def] riscv_kernel_trap_entry_post_to_bir_thm
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
 ACCEPT_TAC riscv_cont_kernel_trap_entry_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_kernel_trap_entry;
Theorem riscv_cont_kernel_trap_entry_full = GEN_ALL readable_thm;

val _ = export_theory ();
