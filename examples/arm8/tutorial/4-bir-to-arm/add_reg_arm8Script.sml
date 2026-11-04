open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory;
open bir_exp_liftingLib bir_typing_expSyntax;
open bir_typing_expTheory;
open bir_extra_expsTheory;
open bir_lifter_general_auxTheory;
open bir_programSyntax bir_interval_expSyntax;
open bir_program_labelsTheory;
open bir_immTheory;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;

open HolBASimps;
open bir_arm8_backlifterTheory;
open bslSyntax;

val _ = new_theory "add_reg_arm8";

(* whole program *)

Definition add_reg_init_addr_def:
 add_reg_init_addr : word64 = 0x1cw
End

Definition add_reg_end_addr_def:
 add_reg_end_addr : word64 = 0x48w
End

(* loop *)

Definition add_reg_init_loop_addr_def:
 add_reg_loop_init_addr : word64 = 0x20w
End

Definition add_reg_end_loop_addr_def:
 add_reg_loop_end_addr : word64 = 0x40w
End

(* contract *)

val y_var = ``(m.REG 5w)``;
val x_var = ``(m.REG 4w)``;
val ly_var = ``(m.REG 3w)``;
val lx_var = ``(m.REG 2w)``;

Definition arm8_add_reg_pre_def:
arm8_add_reg_pre m =
 ((^x_var >= 0w) /\ (^x_var = ^lx_var) /\ (^y_var = ^ly_var))
End

Definition arm8_add_reg_post_def:
 arm8_add_reg_post m =
  ((^x_var + ^y_var) = ^ly_var)
End

val _ = export_theory ();
