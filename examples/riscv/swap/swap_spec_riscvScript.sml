open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
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

val _ = new_theory "swap_spec_riscv";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition swap_init_addr_def:
 swap_init_addr : word64 = 0x10488w
End

Definition swap_end_addr_def:
 swap_end_addr : word64 = 0x1049cw
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_swap_pre_def:
 riscv_swap_pre (pre_x10:word64) (pre_x11:word64)
  (pre_x10_deref:word64) (pre_x11_deref:word64)
  (m:riscv_state) : bool =
  (^(mem_addrs_aligned_prog_disj_riscv_tm mem_params_standard "pre_x10") /\
   m.c_gpr m.procID 10w = pre_x10 /\
   riscv_mem_load_dword m.MEM8 pre_x10 = pre_x10_deref /\
   ^(mem_addrs_aligned_prog_disj_riscv_tm mem_params_standard "pre_x11") /\
   m.c_gpr m.procID 11w = pre_x11 /\
   riscv_mem_load_dword m.MEM8 pre_x11 = pre_x11_deref)
End

Definition riscv_swap_post_def:
 riscv_swap_post (pre_x10:word64) (pre_x11:word64)
  (pre_x10_deref:word64) (pre_x11_deref:word64)
  (m:riscv_state) : bool =
  (riscv_mem_load_dword m.MEM8 pre_x10 = pre_x11_deref /\
   riscv_mem_load_dword m.MEM8 pre_x11 = pre_x10_deref)
End

val _ = export_theory ();
