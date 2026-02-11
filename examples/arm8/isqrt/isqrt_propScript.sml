open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_arm8_backlifterTheory;
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
open isqrt_spec_arm8Theory;
open isqrt_spec_birTheory;
open isqrt_symb_transfTheory;

val _ = new_theory "isqrt_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val arm8_cont_isqrt_1_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_1
  bir_isqrt_progbin_def
  arm8_isqrt_pre_1_def arm8_isqrt_post_1_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_1_def]
  bspec_isqrt_pre_1_def isqrt_arm8_pre_1_imp_bspec_pre_1_thm
  [bspec_isqrt_post_1_def] isqrt_arm8_post_1_imp_bspec_post_1_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_1:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1}
  (arm8_isqrt_pre_1 pre_x0)
  (arm8_isqrt_post_1 pre_x0)
Proof
 rw [isqrt_init_addr_1_def,isqrt_end_addr_1_def] >>
 ACCEPT_TAC arm8_cont_isqrt_1_thm
QED

val arm8_cont_isqrt_2_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_2
  bir_isqrt_progbin_def
  arm8_isqrt_pre_2_def arm8_isqrt_post_2_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_2_def]
  bspec_isqrt_pre_2_def isqrt_arm8_pre_2_imp_bspec_pre_2_thm
  [bspec_isqrt_post_2_def] isqrt_arm8_post_2_imp_bspec_post_2_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_2:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2}
  (arm8_isqrt_pre_2 pre_x1 pre_x3)
  (arm8_isqrt_post_2 pre_x1 pre_x3)
Proof
 rw [isqrt_init_addr_2_def,isqrt_end_addr_2_def] >>
 ACCEPT_TAC arm8_cont_isqrt_2_thm
QED

val arm8_cont_isqrt_3_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_3
  bir_isqrt_progbin_def
  arm8_isqrt_pre_3_def arm8_isqrt_post_3_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_3_def]
  bspec_isqrt_pre_3_def isqrt_arm8_pre_3_imp_bspec_pre_3_thm
  [bspec_isqrt_post_3_loop_def,bspec_isqrt_post_3_ret_def] isqrt_arm8_post_3_imp_bspec_post_3_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_3:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}
  (arm8_isqrt_pre_3 pre_x1 pre_x2 pre_x3)
  (arm8_isqrt_post_3 pre_x1 pre_x2 pre_x3)
Proof
 rw [isqrt_init_addr_3_def,isqrt_end_addr_3_loop_def,isqrt_end_addr_3_ret_def] >>
 ACCEPT_TAC arm8_cont_isqrt_3_thm
QED

val _ = export_theory ();
