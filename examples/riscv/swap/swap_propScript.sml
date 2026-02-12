open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
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

open swapTheory;
open swap_spec_riscvTheory;
open swap_spec_birTheory;
open swap_symb_transfTheory;

val _ = new_theory "swap_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_swap_thm =
 get_riscv_contract_thm
  bspec_cont_swap swap_init_addr_def [swap_end_addr_def]
  bir_swap_progbin_def
  riscv_swap_pre_def riscv_swap_post_def
  bir_swap_prog_def
  [bspec_swap_pre_def]
  bspec_swap_pre_def swap_riscv_pre_imp_bspec_pre_thm
  [bspec_swap_post_def] swap_riscv_post_imp_bspec_post_thm
  bir_swap_riscv_lift_THM;

Theorem riscv_cont_swap:
 riscv_cont bir_swap_progbin swap_init_addr {swap_end_addr}
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
  (riscv_swap_post pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
Proof
 ACCEPT_TAC riscv_cont_swap_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_swap;

Theorem riscv_cont_swap_full = GEN_ALL readable_thm;

val _ = export_theory ();
