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

open tutorial_smtSupportLib;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open incr_memTheory;
open incr_mem_specTheory;
open incr_mem_symb_transfTheory;

val _ = new_theory "incr_mem_prop";

(* ------------------------------------ *)
(* Backlifting BSPEC contract to RISC-V *)
(* ------------------------------------ *)

val riscv_cont_incr_mem_thm =
 get_riscv_contract_sing
  bspec_cont_incr_mem
  ``bir_incr_mem_progbin``
  ``riscv_incr_mem_pre pre_x10 pre_x10_deref``
  ``riscv_incr_mem_post pre_x10 pre_x10_deref``
  bir_incr_mem_prog_def
  [bspec_incr_mem_pre_def]
  bspec_incr_mem_pre_def incr_mem_riscv_pre_imp_bspec_pre_thm
  [bspec_incr_mem_post_def] incr_mem_riscv_post_imp_bspec_post_thm
  bir_incr_mem_riscv_lift_THM;

Theorem riscv_cont_incr_mem:
 riscv_cont bir_incr_mem_progbin incr_mem_init_addr {incr_mem_end_addr}
  (riscv_incr_mem_pre pre_x10 pre_x10_deref)
  (riscv_incr_mem_post pre_x10 pre_x10_deref)
Proof
 rw [incr_mem_init_addr_def,incr_mem_end_addr_def] >>
 ACCEPT_TAC riscv_cont_incr_mem_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_CONV [``riscv_weak_trs``] (concl riscv_cont_incr_mem);

Theorem riscv_cont_incr_mem_full:
  !pre_x10 pre_x10_deref. ^((snd o dest_eq o concl) readable_thm)
Proof
 METIS_TAC [riscv_cont_incr_mem, readable_thm]
QED

val _ = export_theory ();
