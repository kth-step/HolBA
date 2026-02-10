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

open swapTheory;
open swap_spec_arm8Theory;
open swap_spec_birTheory;
open swap_symb_transfTheory;

val _ = new_theory "swap_prop";

(* --------------------------------- *)
(* Backlifting BIR contract to ARMv8 *)
(* --------------------------------- *)

val arm8_cont_swap_thm =
 get_arm8_contract_thm
  bspec_cont_swap
  bir_swap_progbin_def
  arm8_swap_pre_def arm8_swap_post_def
  bir_swap_prog_def
  [bspec_swap_pre_def]
  bspec_swap_pre_def swap_arm8_pre_imp_bspec_pre_thm
  [bspec_swap_post_def] swap_arm8_post_imp_bspec_post_thm
  bir_swap_arm8_lift_THM;

Theorem arm8_cont_swap:
 arm8_cont bir_swap_progbin swap_init_addr {swap_end_addr}
  (arm8_swap_pre pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
  (arm8_swap_post pre_x0 pre_x1 pre_x0_deref pre_x1_deref)
Proof
 rw [swap_init_addr_def,swap_end_addr_def] >>
 ACCEPT_TAC arm8_cont_swap_thm
QED

(* ----------------------- *)
(* Unfolded ARMv8 contract *)
(* ----------------------- *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``arm8_weak_trs``] arm8_cont_swap;
Theorem arm8_cont_swap_full = GEN_ALL readable_thm;

val _ = export_theory ();
