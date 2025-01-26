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

val _ = new_theory "kernel_trap_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition kernel_trap_entry_init_addr_def:
 kernel_trap_entry_init_addr : word64 = 0x800000e0w
End

Definition kernel_trap_entry_end_addr_def:
 kernel_trap_entry_end_addr : word64 = 0x80000190w
End

Definition kernel_trap_return_init_addr_def:
 kernel_trap_return_init_addr : word64 = 0x800001dcw
End

Definition kernel_trap_return_end_addr_def:
 kernel_trap_return_end_addr : word64 = 0x80000268w
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

(*
Definition riscv_kernel_trap_pre_def:
 riscv_kernel_trap_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_kernel_trap_post_def:
 riscv_kernel_trap_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 + 1w)
End
*)

(* ------------------------- *)
(* BSPEC trap_entry contract *)
(* ------------------------- *)

val bspec_kernel_trap_entry_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "MPRV" (BType_Imm Bit8)))
    (BExp_Const (Imm8 3w))``,

  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "mscratch",

 ``BExp_unchanged_mem_interval_distinct Bit64
    (0x800000e0 - 256) 0x80000268
    (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
    8``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mscratch))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x1" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x1))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x2" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x2))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x3" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x3))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x4" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x4))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x5" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x5))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x6" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x6))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x7" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x7))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x8" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x8))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x9" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x9))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x10" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x10))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x11" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x11))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x12" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x12))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x13" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x13))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x14" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x14))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x15" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x15))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x16" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x16))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x17" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x17))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x18" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x18))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x19" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x19))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x20" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x20))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x21" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x21))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x22" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x22))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x23" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x23))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x24" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x24))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x25" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x25))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x26" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x26))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x27" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x27))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x28" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x28))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x29" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x29))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x30" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x30))``,

   ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x31" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x31))``
]

Definition bspec_kernel_trap_entry_pre_def:
 bspec_kernel_trap_entry_pre
  (pre_mscratch:word64)
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
 : bir_exp_t =
  ^bspec_kernel_trap_entry_pre_tm
End

val bspec_kernel_trap_entry_post_tm = bslSyntax.bandl [
 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 16w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x1))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 24w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x2))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 32w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x3))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 40w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x4))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 48w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x5))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 56w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x6))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 64w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x7))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 72w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x8))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 80w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x9))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 96w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x11))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 104w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x12))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 112w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x13))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 120w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x14))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 128w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x15))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 136w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x16))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 144w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x17))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 152w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x18))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 160w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x19))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 168w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x20))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 176w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x21))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 184w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x22))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 192w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x23))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 200w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x24))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 208w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x25))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 216w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x26))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 224w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x27))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 232w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x28))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 240w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x29))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 248w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x30))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 256w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x31))``
]

Definition bspec_kernel_trap_entry_post_def:
 bspec_kernel_trap_entry_post
  (pre_mscratch:word64)
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
 : bir_exp_t =
  ^bspec_kernel_trap_entry_post_tm
End

(* -------------------------- *)
(* BSPEC trap_return contract *)
(* -------------------------- *)

val bspec_kernel_trap_return_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "MPRV" (BType_Imm Bit8)))
    (BExp_Const (Imm8 3w))``,

  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mscratch))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x10" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_x10))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 8w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_mepc_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 16w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x1_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 24w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x2_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 32w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x3_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 40w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x4_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 48w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x5_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 56w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x6_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 64w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x7_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 72w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x8_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 80w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x9_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 88w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x10_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 96w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x11_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 104w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x12_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 112w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x13_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 120w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x14_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 128w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x15_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 136w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x16_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 144w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x17_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 152w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x18_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 160w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x19_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 168w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x20_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 176w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x21_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 184w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x22_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 192w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x23_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 200w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x24_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 208w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x25_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 216w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x26_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 224w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x27_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 232w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x28_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 240w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x29_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 248w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x30_mem))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 256w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x31_mem))``
]

Definition bspec_kernel_trap_return_pre_def:
 bspec_kernel_trap_return_pre
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
 : bir_exp_t =
  ^bspec_kernel_trap_return_pre_tm
End

val bspec_kernel_trap_return_post_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "mepc" (BType_Imm Bit64)))
    (BExp_BinExp BIExp_And
     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFCw))
     (BExp_Const (Imm64 pre_mepc_mem)))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x2_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x4" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x4_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x5" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x5_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x6" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x6_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x7" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x7_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x8" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x8_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x9" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x9_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x11" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x11_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x12" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x12_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x16" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x16_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x17" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x17_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x18" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x18_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x19" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x19_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x20" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x20_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x21" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x21_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x22" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x22_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x23" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x23_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x24" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x24_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x25" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x25_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x26" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x26_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x27" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x27_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x28" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x28_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x29" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x29_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x30" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x30_mem))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x31" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x31_mem))``
];

Definition bspec_kernel_trap_return_post_def:
 bspec_kernel_trap_return_post
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
 : bir_exp_t =
 ^bspec_kernel_trap_return_post_tm
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

val _ = export_theory ();
