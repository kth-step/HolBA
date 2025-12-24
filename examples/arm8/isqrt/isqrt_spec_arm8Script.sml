open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
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

val _ = new_theory "isqrt_spec_arm8";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x718w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x734w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x718w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x720w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x720w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x72cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x72cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x720w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x734w
End

(* --------------- *)
(* ARMv8 contracts *)
(* --------------- *)

(* before loop contract *)

Definition arm8_isqrt_pre_1_def:
 arm8_isqrt_pre_1 (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0)
End

Definition arm8_isqrt_post_1_def:
 arm8_isqrt_post_1 (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = 0w /\ ms.REG 3w = pre_x0)
End

(* loop body contract *)

Definition arm8_isqrt_pre_2_def:
 arm8_isqrt_pre_2 (pre_x1:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = pre_x1 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_isqrt_post_2_def:
 arm8_isqrt_post_2 (pre_x1:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x1 /\
   ms.REG 1w = pre_x1 + 1w /\
   ms.REG 2w = (pre_x1 + 1w) * (pre_x1 + 1w) /\
   ms.REG 3w = pre_x3)
End

(* loop branch contract *)

Definition arm8_isqrt_pre_3_def:
 arm8_isqrt_pre_3 (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_isqrt_post_3_loop_def:
 arm8_isqrt_post_3_loop (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   pre_x2 <=+ pre_x3)
End

Definition arm8_isqrt_post_3_ret_def:
 arm8_isqrt_post_3_ret (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   pre_x3 <+ pre_x2)
End

Definition arm8_isqrt_post_3_def:
 arm8_isqrt_post_3 (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  if ms.PC = isqrt_end_addr_3_loop then
    arm8_isqrt_post_3_loop pre_x1 pre_x2 pre_x3 ms
  else if ms.PC = isqrt_end_addr_3_ret then
    arm8_isqrt_post_3_ret pre_x1 pre_x2 pre_x3 ms
  else F
End

val _ = export_theory ();
