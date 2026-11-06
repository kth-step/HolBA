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

open update_satTheory;
open update_sat_spec_arm8Theory;
open update_sat_spec_birTheory;
open update_sat_symb_transfTheory;

val _ = new_theory "update_sat_prop";

(* --------------------------------- *)
(* Backlifting BIR contract to ARMv8 *)
(* --------------------------------- *)

val arm8_cont_update_sat_thm =
 get_arm8_contract_thm
  bspec_cont_update_sat update_sat_init_addr_def [update_sat_end_addr_def]
  bir_update_sat_progbin_def
  arm8_update_sat_pre_def arm8_update_sat_post_def
  bir_update_sat_prog_def
  [bspec_update_sat_pre_def]
  bspec_update_sat_pre_def arm8_update_sat_pre_to_bir_thm
  [bspec_update_sat_post_def] arm8_update_sat_post_to_bir_thm
  bir_update_sat_arm8_lift_THM;

Theorem arm8_cont_update_sat:
 arm8_cont bir_update_sat_progbin update_sat_init_addr {update_sat_end_addr}
  (arm8_update_sat_pre pre_x0 pre_x1 pre_x2 pre_x3)
  (arm8_update_sat_post pre_x0 pre_x1 pre_x2 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_update_sat_thm
QED

(* ------------------------ *)
(* Unfolded ARMv8 contract  *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``arm8_weak_trs``] arm8_cont_update_sat;

Theorem arm8_cont_update_sat_full = GEN_ALL readable_thm;

val _ = export_theory ();
