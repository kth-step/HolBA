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

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_incr_mem_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_incr_mem_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_incr_mem_post_def;

(* ------------------------------------ *)
(* Backlifting BSPEC contract to RISC-V *)
(* ------------------------------------ *)

val riscv_cont_incr_mem_thm =
 get_riscv_contract_sing
  bspec_cont_incr_mem
  progbin_tm riscv_pre_tm riscv_post_tm
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

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_incr_mem;
Theorem riscv_cont_incr_mem_full = GEN_ALL readable_thm;

val _ = export_theory ();
