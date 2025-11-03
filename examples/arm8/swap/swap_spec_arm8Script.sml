open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

val _ = new_theory "swap_spec_arm8";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition swap_init_addr_def:
 swap_init_addr : word64 = 0x718w
End

Definition swap_end_addr_def:
 swap_end_addr : word64 = 0x730w
End

(* --------------- *)
(* ARMv8 contract *)
(* --------------- *)

Definition arm8_swap_pre_def:
 arm8_swap_pre (pre_x0:word64) (pre_x1:word64)
  (pre_x0_deref:word64) (pre_x1_deref:word64)
  (ms:arm8_state) : bool =
 (^(mem_addrs_aligned_prog_disj_arm8_tm mem_params_standard "pre_x0") /\
  ms.REG 0w = pre_x0 /\
  arm8_load_64 ms.MEM pre_x0 = pre_x0_deref /\
  ^(mem_addrs_aligned_prog_disj_arm8_tm mem_params_standard "pre_x1") /\
  ms.REG 1w = pre_x1 /\
  arm8_load_64 ms.MEM pre_x1 = pre_x1_deref)
End

Definition arm8_swap_post_def:
 arm8_swap_post (pre_x0:word64) (pre_x1:word64)
  (pre_x0_deref:word64) (pre_x1_deref:word64)
  (ms:arm8_state) : bool =
  (arm8_load_64 ms.MEM pre_x0 = pre_x1_deref /\
   arm8_load_64 ms.MEM pre_x1 = pre_x0_deref)
End

val _ = export_theory ();
