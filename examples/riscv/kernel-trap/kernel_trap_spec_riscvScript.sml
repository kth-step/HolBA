open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;

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

val _ = new_theory "kernel_trap_spec_riscv";

(* ---------------------------------- *)
(* Program boundaries for trap_entry  *)
(* ---------------------------------- *)

Definition kernel_trap_entry_init_addr_def:
 kernel_trap_entry_init_addr : word64 = 0x800000e0w
End

Definition kernel_trap_entry_end_addr_def:
 kernel_trap_entry_end_addr : word64 = 0x80000190w
End

(* ---------------------------------- *)
(* Program boundaries for trap_return *)
(* ---------------------------------- *)

Definition kernel_trap_return_init_addr_def:
 kernel_trap_return_init_addr : word64 = 0x800001dcw
End

Definition kernel_trap_return_end_addr_def:
 kernel_trap_return_end_addr : word64 = 0x80000268w
End

(* -------------------------- *)
(* RISC-V trap_entry contract *)
(* -------------------------- *)

Definition riscv_kernel_trap_entry_pre_def:
 riscv_kernel_trap_entry_pre
  (pre_mscratch:word64) (pre_mepc:word64)
  (pre_mcause:word64) (pre_mhartid:word64)
  (pre_mtval:word64)
  (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (pre_x4:word64)
  (pre_x5:word64) (pre_x6:word64)
  (pre_x7:word64) (pre_x8:word64)
  (pre_x9:word64) (pre_x10:word64)
  (pre_x11:word64) (pre_x12:word64)
  (pre_x13:word64) (pre_x14:word64)
  (pre_x15:word64) (pre_x16:word64)
  (pre_x17:word64) (pre_x18:word64)
  (pre_x19:word64) (pre_x20:word64)
  (pre_x21:word64) (pre_x22:word64)
  (pre_x23:word64) (pre_x24:word64)
  (pre_x25:word64) (pre_x26:word64)
  (pre_x27:word64) (pre_x28:word64)
  (pre_x29:word64) (pre_x30:word64)
  (pre_x31:word64)
  (m:riscv_state)
 : bool =
 ((m.c_MCSR m.procID).mstatus.MPRV = 3w /\
  ^(mem_addrs_aligned_prog_disj_riscv_tm mem_params_standard "pre_mscratch") /\
  (pre_mscratch ≤₊ 0xFFFFFFFFFFFFFFF7w /\
    ((0x7FFFFFE0w <₊ pre_mscratch \/ 8w + pre_mscratch ≤₊ 0x7FFFFFE0w) /\
     (pre_mscratch <₊ 0x7FFFFFE0w \/ 0x80000268w ≤₊ pre_mscratch))) /\
  (m.c_MCSR m.procID).mscratch = pre_mscratch /\
  (m.c_MCSR m.procID).mepc = pre_mepc /\
  (reg'mcause $ (m.c_MCSR m.procID).mcause) = pre_mcause /\
  (m.c_MCSR m.procID).mhartid = pre_mhartid /\
  (m.c_MCSR m.procID).mtval = pre_mtval /\
  m.c_gpr m.procID 1w = pre_x1 /\
  m.c_gpr m.procID 2w = pre_x2 /\
  m.c_gpr m.procID 3w = pre_x3 /\
  m.c_gpr m.procID 4w = pre_x4 /\
  m.c_gpr m.procID 5w = pre_x5 /\
  m.c_gpr m.procID 6w = pre_x6 /\
  m.c_gpr m.procID 7w = pre_x7 /\
  m.c_gpr m.procID 8w = pre_x8 /\
  m.c_gpr m.procID 9w = pre_x9 /\
  m.c_gpr m.procID 10w = pre_x10 /\
  m.c_gpr m.procID 11w = pre_x11 /\
  m.c_gpr m.procID 12w = pre_x12 /\
  m.c_gpr m.procID 13w = pre_x13 /\
  m.c_gpr m.procID 14w = pre_x14 /\
  m.c_gpr m.procID 15w = pre_x15 /\
  m.c_gpr m.procID 16w = pre_x16 /\
  m.c_gpr m.procID 17w = pre_x17 /\
  m.c_gpr m.procID 18w = pre_x18 /\
  m.c_gpr m.procID 19w = pre_x19 /\
  m.c_gpr m.procID 20w = pre_x20 /\
  m.c_gpr m.procID 21w = pre_x21 /\
  m.c_gpr m.procID 22w = pre_x22 /\
  m.c_gpr m.procID 23w = pre_x23 /\
  m.c_gpr m.procID 24w = pre_x24 /\
  m.c_gpr m.procID 25w = pre_x25 /\
  m.c_gpr m.procID 26w = pre_x26 /\
  m.c_gpr m.procID 27w = pre_x27 /\
  m.c_gpr m.procID 28w = pre_x28 /\
  m.c_gpr m.procID 29w = pre_x29 /\
  m.c_gpr m.procID 30w = pre_x30 /\
  m.c_gpr m.procID 31w = pre_x31)
End

Definition riscv_kernel_trap_entry_post_def:
 riscv_kernel_trap_entry_post
  (pre_mscratch:word64) (pre_mepc:word64)
  (pre_mcause:word64) (pre_mhartid:word64)
  (pre_mtval:word64)
  (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (pre_x4:word64)
  (pre_x5:word64) (pre_x6:word64)
  (pre_x7:word64) (pre_x8:word64)
  (pre_x9:word64) (pre_x10:word64)
  (pre_x11:word64) (pre_x12:word64)
  (pre_x13:word64) (pre_x14:word64)
  (pre_x15:word64) (pre_x16:word64)
  (pre_x17:word64) (pre_x18:word64)
  (pre_x19:word64) (pre_x20:word64)
  (pre_x21:word64) (pre_x22:word64)
  (pre_x23:word64) (pre_x24:word64)
  (pre_x25:word64) (pre_x26:word64)
  (pre_x27:word64) (pre_x28:word64)
  (pre_x29:word64) (pre_x30:word64)
  (pre_x31:word64)
  (m:riscv_state)
 : bool =
 ((m.c_MCSR m.procID).mscratch = pre_x10 /\
  m.c_gpr m.procID 2w =
   (0xFFFFFFFFFFFFFFFFw * (pre_mhartid <<~ 10w)) + 0x80006400w /\
  m.c_gpr m.procID 3w = 0x80005804w /\
  m.c_gpr m.procID 10w = pre_mscratch /\
  m.c_gpr m.procID 11w = pre_mcause /\
  m.c_gpr m.procID 12w = pre_mtval /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 8w) = pre_mepc /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 16w) = pre_x1 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 24w) = pre_x2 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 32w) = pre_x3 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 40w) = pre_x4 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 48w) = pre_x5 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 56w) = pre_x6 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 64w) = pre_x7 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 72w) = pre_x8 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 80w) = pre_x9 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 88w) = pre_x10 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 96w) = pre_x11 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 104w) = pre_x12 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 112w) = pre_x13 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 120w) = pre_x14 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 128w) = pre_x15 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 136w) = pre_x16 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 144w) = pre_x17 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 152w) = pre_x18 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 160w) = pre_x19 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 168w) = pre_x20 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 176w) = pre_x21 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 184w) = pre_x22 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 192w) = pre_x23 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 200w) = pre_x24 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 208w) = pre_x25 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 216w) = pre_x26 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 224w) = pre_x27 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 232w) = pre_x28 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 240w) = pre_x29 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 248w) = pre_x30 /\
  riscv_mem_load_dword m.MEM8 (pre_mscratch + 256w) = pre_x31)
End

(* --------------------------- *)
(* RISC-V trap_return contract *)
(* --------------------------- *)

Definition riscv_kernel_trap_return_pre_def:
 riscv_kernel_trap_return_pre
 (pre_mscratch:word64) (pre_x10:word64)
 (pre_mepc_mem:word64)
 (pre_x1_mem:word64) (pre_x2_mem:word64)
 (pre_x3_mem:word64) (pre_x4_mem:word64)
 (pre_x5_mem:word64) (pre_x6_mem:word64)
 (pre_x7_mem:word64) (pre_x8_mem:word64)
 (pre_x9_mem:word64) (pre_x10_mem:word64)
 (pre_x11_mem:word64) (pre_x12_mem:word64)
 (pre_x13_mem:word64) (pre_x14_mem:word64)
 (pre_x15_mem:word64) (pre_x16_mem:word64)
 (pre_x17_mem:word64) (pre_x18_mem:word64)
 (pre_x19_mem:word64) (pre_x20_mem:word64)
 (pre_x21_mem:word64) (pre_x22_mem:word64)
 (pre_x23_mem:word64) (pre_x24_mem:word64)
 (pre_x25_mem:word64) (pre_x26_mem:word64)
 (pre_x27_mem:word64) (pre_x28_mem:word64)
 (pre_x29_mem:word64) (pre_x30_mem:word64)
 (pre_x31_mem:word64)
 (m:riscv_state)
 : bool =
 ((m.c_MCSR m.procID).mstatus.MPRV = 3w /\
  ^(mem_addrs_aligned_prog_disj_riscv_tm mem_params_standard "pre_x10") /\
  (m.c_MCSR m.procID).mscratch = pre_mscratch /\
  m.c_gpr m.procID 10w = pre_x10 /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 8w) = pre_mepc_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 16w) = pre_x1_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 24w) = pre_x2_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 32w) = pre_x3_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 40w) = pre_x4_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 48w) = pre_x5_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 56w) = pre_x6_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 64w) = pre_x7_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 72w) = pre_x8_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 80w) = pre_x9_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 88w) = pre_x10_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 96w) = pre_x11_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 104w) = pre_x12_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 112w) = pre_x13_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 120w) = pre_x14_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 128w) = pre_x15_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 136w) = pre_x16_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 144w) = pre_x17_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 152w) = pre_x18_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 160w) = pre_x19_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 168w) = pre_x20_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 176w) = pre_x21_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 184w) = pre_x22_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 192w) = pre_x23_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 200w) = pre_x24_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 208w) = pre_x25_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 216w) = pre_x26_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 224w) = pre_x27_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 232w) = pre_x28_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 240w) = pre_x29_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 248w) = pre_x30_mem /\
  riscv_mem_load_dword m.MEM8 (pre_x10 + 256w) = pre_x31_mem)
End

Definition riscv_kernel_trap_return_post_def:
 riscv_kernel_trap_return_post
 (pre_mscratch:word64) (pre_x10:word64)
 (pre_mepc_mem:word64)
 (pre_x1_mem:word64) (pre_x2_mem:word64)
 (pre_x3_mem:word64) (pre_x4_mem:word64)
 (pre_x5_mem:word64) (pre_x6_mem:word64)
 (pre_x7_mem:word64) (pre_x8_mem:word64)
 (pre_x9_mem:word64) (pre_x10_mem:word64)
 (pre_x11_mem:word64) (pre_x12_mem:word64)
 (pre_x13_mem:word64) (pre_x14_mem:word64)
 (pre_x15_mem:word64) (pre_x16_mem:word64)
 (pre_x17_mem:word64) (pre_x18_mem:word64)
 (pre_x19_mem:word64) (pre_x20_mem:word64)
 (pre_x21_mem:word64) (pre_x22_mem:word64)
 (pre_x23_mem:word64) (pre_x24_mem:word64)
 (pre_x25_mem:word64) (pre_x26_mem:word64)
 (pre_x27_mem:word64) (pre_x28_mem:word64)
 (pre_x29_mem:word64) (pre_x30_mem:word64)
 (pre_x31_mem:word64)
 (m:riscv_state)
 : bool =
 ((m.c_MCSR m.procID).mscratch = pre_x10 /\
  (m.c_MCSR m.procID).mepc = 0xFFFFFFFFFFFFFFFCw && pre_mepc_mem /\
  m.c_gpr m.procID 1w = pre_x1_mem /\
  m.c_gpr m.procID 2w = pre_x2_mem /\
  m.c_gpr m.procID 3w = pre_x3_mem /\
  m.c_gpr m.procID 4w = pre_x4_mem /\
  m.c_gpr m.procID 5w = pre_x5_mem /\
  m.c_gpr m.procID 6w = pre_x6_mem /\
  m.c_gpr m.procID 7w = pre_x7_mem /\
  m.c_gpr m.procID 8w = pre_x8_mem /\
  m.c_gpr m.procID 9w = pre_x9_mem /\
  m.c_gpr m.procID 10w = pre_x10_mem /\
  m.c_gpr m.procID 11w = pre_x11_mem /\
  m.c_gpr m.procID 12w = pre_x12_mem /\
  m.c_gpr m.procID 13w = pre_x13_mem /\
  m.c_gpr m.procID 14w = pre_x14_mem /\
  m.c_gpr m.procID 15w = pre_x15_mem /\
  m.c_gpr m.procID 16w = pre_x16_mem /\
  m.c_gpr m.procID 17w = pre_x17_mem /\
  m.c_gpr m.procID 18w = pre_x18_mem /\
  m.c_gpr m.procID 19w = pre_x19_mem /\
  m.c_gpr m.procID 20w = pre_x20_mem /\
  m.c_gpr m.procID 21w = pre_x21_mem /\
  m.c_gpr m.procID 22w = pre_x22_mem /\
  m.c_gpr m.procID 23w = pre_x23_mem /\
  m.c_gpr m.procID 24w = pre_x24_mem /\
  m.c_gpr m.procID 25w = pre_x25_mem /\
  m.c_gpr m.procID 26w = pre_x26_mem /\
  m.c_gpr m.procID 27w = pre_x27_mem /\
  m.c_gpr m.procID 28w = pre_x28_mem /\
  m.c_gpr m.procID 29w = pre_x29_mem /\
  m.c_gpr m.procID 30w = pre_x30_mem /\
  m.c_gpr m.procID 31w = pre_x31_mem)
End

val _ = export_theory ();
