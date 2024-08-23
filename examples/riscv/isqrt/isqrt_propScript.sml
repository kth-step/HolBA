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

open isqrtTheory;
open isqrt_specTheory;
open isqrt_symb_transfTheory;

val _ = new_theory "isqrt_prop";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_isqrt_progbin_def;

val riscv_pre_1_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_1_def;
val riscv_post_1_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_1_def;

val riscv_pre_2_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_2_def;
val riscv_post_2_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_2_def;

val riscv_pre_3_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_3_def;
val riscv_post_3_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_3_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_isqrt_1_thm =
 get_riscv_contract
  bspec_cont_isqrt_1
  progbin_tm riscv_pre_1_tm riscv_post_1_tm
  bir_isqrt_prog_def
  [bspec_isqrt_pre_1_def]
  bspec_isqrt_pre_1_def isqrt_riscv_pre_1_imp_bspec_pre_1_thm
  [bspec_isqrt_post_1_def] isqrt_riscv_post_1_imp_bspec_post_1_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_1:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1}
  (riscv_isqrt_pre_1 pre_x10)
  (riscv_isqrt_post_1 pre_x10)
Proof
 rw [isqrt_init_addr_1_def,isqrt_end_addr_1_def] >>
 ACCEPT_TAC riscv_cont_isqrt_1_thm
QED

val riscv_cont_isqrt_2_thm =
 get_riscv_contract
  bspec_cont_isqrt_2
  progbin_tm riscv_pre_2_tm riscv_post_2_tm
  bir_isqrt_prog_def
  [bspec_isqrt_pre_2_def]
  bspec_isqrt_pre_2_def isqrt_riscv_pre_2_imp_bspec_pre_2_thm
  [bspec_isqrt_post_2_def] isqrt_riscv_post_2_imp_bspec_post_2_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_2:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2}
  (riscv_isqrt_pre_2 pre_x13 pre_x15)
  (riscv_isqrt_post_2 pre_x13 pre_x15)
Proof
 rw [isqrt_init_addr_2_def,isqrt_end_addr_2_def] >>
 ACCEPT_TAC riscv_cont_isqrt_2_thm
QED

val riscv_cont_isqrt_3_thm =
 get_riscv_contract
  bspec_cont_isqrt_3
  progbin_tm riscv_pre_3_tm riscv_post_3_tm
  bir_isqrt_prog_def
  [bspec_isqrt_pre_3_def]
  bspec_isqrt_pre_3_def isqrt_riscv_pre_3_imp_bspec_pre_3_thm
  [bspec_isqrt_post_3_loop_def,bspec_isqrt_post_3_ret_def] isqrt_riscv_post_3_imp_bspec_post_3_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_3:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14)
  (riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14)
Proof
 rw [isqrt_init_addr_3_def,isqrt_end_addr_3_loop_def,isqrt_end_addr_3_ret_def] >>
 ACCEPT_TAC riscv_cont_isqrt_3_thm
QED

val _ = export_theory ();
