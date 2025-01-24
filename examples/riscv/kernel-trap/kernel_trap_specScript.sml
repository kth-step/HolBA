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

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

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
     (BExp_Const (Imm64 pre_x17))``
]

Definition bspec_kernel_trap_entry_pre_def:
 bspec_kernel_trap_entry_pre
  (pre_mscratch:word64)
  (pre_x1:word64) (pre_x2:word64) (pre_x3:word64)
  (pre_x11:word64) (pre_x12:word64)
  (pre_x13:word64) (pre_x14:word64) (pre_x15:word64)
  (pre_x16:word64) (pre_x17:word64) : bir_exp_t =
  ^bspec_kernel_trap_entry_pre_tm
End

val bspec_kernel_trap_entry_post_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 16w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x1))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 24w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x2))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 32w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x3))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 96w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x11))``
]

Definition bspec_kernel_trap_entry_post_def:
 bspec_kernel_trap_entry_post
  (pre_mscratch:word64)
  (pre_x1:word64) (pre_x2:word64) (pre_x3:word64)
  (pre_x11:word64) (pre_x12:word64) (pre_x13:word64)
  (pre_x14:word64) (pre_x15:word64) (pre_x16:word64)
  (pre_x17:word64) : bir_exp_t =
  ^bspec_kernel_trap_entry_post_tm
End

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
       (BExp_Const (Imm64 48w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x5))``,

  ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_x10))
       (BExp_Const (Imm64 56w)))
       BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x6))``
]

Definition bspec_kernel_trap_return_pre_def:
 bspec_kernel_trap_return_pre
 (pre_mscratch:word64)
 (pre_x5:word64) (pre_x6:word64)
 (pre_x10:word64)
 : bir_exp_t =
  ^bspec_kernel_trap_return_pre_tm
End

val bspec_kernel_trap_return_post_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x5" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x5))``,

  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x6" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x6))``
];

Definition bspec_kernel_trap_return_post_def:
 bspec_kernel_trap_return_post
  (pre_mscratch:word64)
  (pre_x5:word64) (pre_x6:word64)
  (pre_x10:word64)
 : bir_exp_t =
 ^bspec_kernel_trap_return_post_tm
End

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

val _ = export_theory ();
