open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_smtLib;

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

val _ = new_theory "max_spec_arm8";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition max_init_addr_def:
 max_init_addr : word64 = 0x718w
End

Definition max_end_addr_def:
 max_end_addr : word64 = 0x720w
End

(* -------------- *)
(* ARMv8 contract *)
(* -------------- *)

Definition arm8_max_pre_def:
 arm8_max_pre (pre_x0:word64) (pre_x1:word64) (m:arm8_state) : bool =
  (m.REG 0w = pre_x0 /\ m.REG 1w = pre_x1)
End

Definition arm8_max_post_def:
 arm8_max_post (pre_x0:word64) (pre_x1:word64) (m:arm8_state) : bool =
  ((m.REG 0w = pre_x0 \/ m.REG 0w = pre_x1) /\
    pre_x0 <=+ m.REG 0w /\
    pre_x1 <=+ m.REG 0w)
End

val _ = export_theory ();
