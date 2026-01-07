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

val _ = new_theory "isqrt_spec_riscv";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x10488w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x104a0w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x10488w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x10490w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x10490w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x1049cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x1049cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x10490w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x104a0w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* before loop contract *)

Definition riscv_isqrt_pre_1_def:
 riscv_isqrt_pre_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_isqrt_post_1_def:
 riscv_isqrt_post_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x10 /\
   m.c_gpr m.procID 15w = 0w)
End

(* loop body contract *)

Definition riscv_isqrt_pre_2_def:
 riscv_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 15w = pre_x15)
End

Definition riscv_isqrt_post_2_def:
 riscv_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x15 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = (pre_x15 + 1w) * (pre_x15 + 1w) /\
   m.c_gpr m.procID 15w = pre_x15 + 1w)
End

(* loop branch contract *)

Definition riscv_isqrt_pre_3_def:
 riscv_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14)
End

Definition riscv_isqrt_post_3_loop_def:
 riscv_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x14 <=+ pre_x13)
End

Definition riscv_isqrt_post_3_ret_def:
 riscv_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x13 <+ pre_x14)
End

Definition riscv_isqrt_post_3_def:
 riscv_isqrt_post_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  if m.c_PC m.procID = isqrt_end_addr_3_loop then
    riscv_isqrt_post_3_loop pre_x10 pre_x13 pre_x14 m
  else if m.c_PC m.procID = isqrt_end_addr_3_ret then
    riscv_isqrt_post_3_ret pre_x10 pre_x13 pre_x14 m
  else F
End

val _ = export_theory ();
