open HolKernel boolLib liteLib simpLib Parse bossLib;

open wordsTheory;

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

open add_regTheory;

val _ = new_theory "add_reg_spec_arm8";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program, excluding the stack frame setup and teardown *)

Definition add_reg_init_addr_def:
 add_reg_init_addr : word64 = 0x1cw
End

Definition add_reg_end_addr_def:
 add_reg_end_addr : word64 = 0x48w
End

(* The loop head is 0x38, where the loop condition is evaluated
   from x2 (mov, cmp, b.gt). At the conditional jump at 0x40, it
   is only available in the flags. *)

(* before loop: jump to the loop head *)

Definition add_reg_init_addr_1_def:
 add_reg_init_addr_1 : word64 = 0x1cw
End

Definition add_reg_end_addr_1_def:
 add_reg_end_addr_1 : word64 = 0x38w
End

(* loop branch *)

Definition add_reg_init_addr_2_def:
 add_reg_init_addr_2 : word64 = 0x38w
End

Definition add_reg_end_addr_2_loop_def:
 add_reg_end_addr_2_loop : word64 = 0x20w
End

Definition add_reg_end_addr_2_ret_def:
 add_reg_end_addr_2_ret : word64 = 0x48w
End

(* loop body *)

Definition add_reg_init_addr_3_def:
 add_reg_init_addr_3 : word64 = 0x20w
End

Definition add_reg_end_addr_3_def:
 add_reg_end_addr_3 : word64 = 0x38w
End

(* --------------- *)
(* ARMv8 contracts *)
(* --------------- *)

(* before loop contract *)

Definition arm8_add_reg_pre_1_def:
 arm8_add_reg_pre_1 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

(* The postconditions of contracts 1 and 3 fix the PC to the end
   label, so that the contracts can also list the loop exit as an
   ending label that is never reached first, as needed for composition *)

Definition arm8_add_reg_post_1_def:
 arm8_add_reg_post_1 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.PC = add_reg_end_addr_1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

(* loop branch contract *)

Definition arm8_add_reg_pre_2_def:
 arm8_add_reg_pre_2 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_add_reg_post_2_loop_def:
 arm8_add_reg_post_2_loop (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   0w < pre_x2)
End

Definition arm8_add_reg_post_2_ret_def:
 arm8_add_reg_post_2_ret (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   pre_x2 <= 0w)
End

Definition arm8_add_reg_post_2_def:
 arm8_add_reg_post_2 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  if ms.PC = add_reg_end_addr_2_loop then
    arm8_add_reg_post_2_loop pre_x2 pre_x3 ms
  else if ms.PC = add_reg_end_addr_2_ret then
    arm8_add_reg_post_2_ret pre_x2 pre_x3 ms
  else F
End

(* loop body contract *)

Definition arm8_add_reg_pre_3_def:
 arm8_add_reg_pre_3 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_add_reg_post_3_def:
 arm8_add_reg_post_3 (pre_x2:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.PC = add_reg_end_addr_3 /\
   ms.REG 2w = pre_x2 - 1w /\
   ms.REG 3w = pre_x3 + 1w)
End

(* ----------------------- *)
(* Whole program contract  *)
(* ----------------------- *)

(* Starting at 0x1c with x2 = x >= 0 and x3 = y, execution reaches
   0x48 with x3 = x + y (signed comparisons, as in add_reg.c) *)

Definition arm8_add_reg_pre_def:
 arm8_add_reg_pre (pre_x : word64) (pre_y : word64) (m : arm8_state) : bool =
  (pre_x >= 0w /\ m.REG 2w = pre_x /\ m.REG 3w = pre_y)
End

Definition arm8_add_reg_post_def:
 arm8_add_reg_post (pre_x : word64) (pre_y : word64) (m : arm8_state) : bool =
  (pre_x + pre_y = m.REG 3w)
End

(* Loop ingredients for proving the whole program contract from the
   three piece contracts with arm8_cont_loop_rule, using loop head
   add_reg_init_addr_2 (0x38) and exit set {add_reg_end_addr} (0x48):

   - contract 1 (with conseq) establishes arm8_add_reg_inv at 0x38
   - iteration: contract 2 (loop exit) then contract 3 from 0x38 back
     to 0x38 under inv /\ cond, decreasing the variant
   - exit: contract 2 (ret exit) from 0x38 to 0x48 under inv /\ ~cond,
     establishing arm8_add_reg_post *)

Definition arm8_add_reg_inv_def:
 arm8_add_reg_inv (pre_x:word64) (pre_y:word64) (ms:arm8_state) : bool =
  (ms.REG 2w + ms.REG 3w = pre_x + pre_y /\
   0w <= ms.REG 2w)
End

Definition arm8_add_reg_cond_def:
 arm8_add_reg_cond (ms:arm8_state) : bool =
  (0w < ms.REG 2w)
End

(* Decreases w.r.t. $< *)
Definition arm8_add_reg_variant_def:
 arm8_add_reg_variant (ms:arm8_state) : num =
  w2n (ms.REG 2w)
End

val _ = export_theory ();
