open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_interval_expTheory;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;
open bir_extra_expsTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open kernel_trap_spec_riscvTheory;

val _ = new_theory "kernel_trap_spec_bir";

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
     (BExp_Den (BVar "mepc" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mepc))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "mcause" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mcause))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "mhartid" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mhartid))``,

  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "mtval" (BType_Imm Bit64)))
     (BExp_Const (Imm64 pre_mtval))``,

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
 : bir_exp_t =
  ^bspec_kernel_trap_entry_pre_tm
End

val bspec_kernel_trap_entry_post_tm = bslSyntax.bandl [
 ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "mscratch" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,

``BExp_BinPred BIExp_Equal
   (BExp_Den (BVar "x2" (BType_Imm Bit64)))
   (BExp_BinExp BIExp_Plus
     (BExp_BinExp BIExp_Mult
       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
       (BExp_BinExp BIExp_LeftShift
         (BExp_Const (Imm64 pre_mhartid))
         (BExp_Const (Imm64 10w))))
     (BExp_Const (Imm64 0x80006400w)))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "x3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 0x80005804w))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_mscratch))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "x11" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_mcause))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "x12" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_mtval))``,

 ``BExp_BinPred BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 pre_mscratch))
      (BExp_Const (Imm64 8w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_mepc))``,

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
      (BExp_Const (Imm64 88w)))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 pre_x10))``,

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

(* ----------------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts for entry *)
(* ----------------------------------------------- *)

Theorem kernel_trap_entry_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
  (bspec_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
Proof
  rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_entry_pre_def] >>    
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [
     bir_extra_expsTheory.BExp_Aligned_def,
     bir_immTheory.n2bs_def,
     BExp_unchanged_mem_interval_distinct_def
    ]) >>
  Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

  Cases_on `bs` >> Cases_on `b0` >>
  
  FULL_SIMP_TAC (std_ss) [
   riscv_kernel_trap_entry_pre_def,
   bspec_kernel_trap_entry_pre_def,
   bir_extra_expsTheory.BExp_Aligned_def
  ] >>
  
  fs [GSYM bir_and_equiv] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def,
   BExp_unchanged_mem_interval_distinct_def,
   bir_val_TF_bool2b_DEF
  ] >>

  rw []
QED

Theorem kernel_trap_entry_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
   (\l. (bspec_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31))
   ls
Proof
 fs [bir_post_bir_to_riscv_def,bspec_kernel_trap_entry_post_def,GSYM bir_and_equiv] >>

 Cases_on `bs` >> Cases_on `b0` >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_mem_eq,
  bir_eval_bin_pred_exists_64_eq
 ] >>

 rw [riscv_kernel_trap_entry_post_def] >>

 METIS_TAC [
  bir_load_from_mem_riscv_mem_load_dword,
  bmr_rel_riscv_MEM8_map,
  riscv_bmr_mscratch_equiv,
  riscv_bmr_x2_equiv,
  riscv_bmr_x3_equiv,
  riscv_bmr_x10_equiv,
  riscv_bmr_x11_equiv,
  riscv_bmr_x12_equiv
 ]
QED

(* ------------------------------------------------ *)
(* Connecting RISC-V and BSPEC contracts for return *)
(* ------------------------------------------------ *)

Theorem kernel_trap_return_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
  (bspec_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
Proof
 rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_return_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_extra_expsTheory.BExp_Aligned_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_immTheory.n2bs_def]) >>

 Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

 Cases_on `bs` >> Cases_on `b0` >>
  
 FULL_SIMP_TAC (std_ss) [riscv_kernel_trap_return_pre_def, bspec_kernel_trap_return_pre_def,bir_extra_expsTheory.BExp_Aligned_def] >>

 fs [GSYM bir_and_equiv] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def
 ] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 8w)) = SOME (Imm64 pre_mepc_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 16w)) = SOME (Imm64 pre_x1_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 24w)) = SOME (Imm64 pre_x2_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 32w)) = SOME (Imm64 pre_x3_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 40w)) = SOME (Imm64 pre_x4_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 48w)) = SOME (Imm64 pre_x5_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 56w)) = SOME (Imm64 pre_x6_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 64w)) = SOME (Imm64 pre_x7_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 72w)) = SOME (Imm64 pre_x8_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 80w)) = SOME (Imm64 pre_x9_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 88w)) = SOME (Imm64 pre_x10_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 96w)) = SOME (Imm64 pre_x11_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 104w)) = SOME (Imm64 pre_x12_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 112w)) = SOME (Imm64 pre_x13_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 120w)) = SOME (Imm64 pre_x14_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 128w)) = SOME (Imm64 pre_x15_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 136w)) = SOME (Imm64 pre_x16_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 144w)) = SOME (Imm64 pre_x17_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 152w)) = SOME (Imm64 pre_x18_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 160w)) = SOME (Imm64 pre_x19_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 168w)) = SOME (Imm64 pre_x20_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 176w)) = SOME (Imm64 pre_x21_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 184w)) = SOME (Imm64 pre_x22_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 192w)) = SOME (Imm64 pre_x23_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 200w)) = SOME (Imm64 pre_x24_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 208w)) = SOME (Imm64 pre_x25_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 216w)) = SOME (Imm64 pre_x26_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 224w)) = SOME (Imm64 pre_x27_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 232w)) = SOME (Imm64 pre_x28_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 240w)) = SOME (Imm64 pre_x29_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 248w)) = SOME (Imm64 pre_x30_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 256w)) = SOME (Imm64 pre_x31_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 rw [bir_eval_bin_pred_64_mem_eq] >>
 fs [riscv_mem_load_dword_bir_load_from_mem,bir_val_true_def]
QED

Theorem kernel_trap_return_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
   (\l. (bspec_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem))
   ls
Proof
 once_rewrite_tac [bir_post_bir_to_riscv_def,bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>

 fs [GSYM bir_and_equiv] >>

 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >>

 rw [bir_eval_bin_pred_exists_64_eq] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_kernel_trap_return_post_def,
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

val _ = export_theory ();
