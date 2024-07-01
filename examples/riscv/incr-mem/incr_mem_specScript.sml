open HolKernel boolLib Parse bossLib;

open markerTheory;

open distribute_generic_stuffLib;

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

open tutorial_smtSupportLib;
open bir_symbLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open incr_memTheory;

open distribute_generic_stuffTheory;

val _ = new_theory "incr_mem_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition incr_mem_init_addr_def:
 incr_mem_init_addr : word64 = 0x00w
End

Definition incr_mem_end_addr_def:
 incr_mem_end_addr : word64 = 0x0cw
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_incr_mem_pre_def:
 riscv_incr_mem_pre (x:word64) (xv:word64) (m:riscv_state) : bool =
  (^(mem_addrs_aligned_prog_disj_riscv_tm "x") /\
   m.c_gpr m.procID 10w = x /\
   riscv_mem_load_dword m.MEM8 x = xv)
End

Definition riscv_incr_mem_post_def:
 riscv_incr_mem_post (x:word64) (xv:word64) (m:riscv_state) : bool =
  (riscv_mem_load_dword m.MEM8 x = xv + 1w)
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_incr_mem_pre_tm = bslSyntax.bandl [
 mem_addrs_aligned_prog_disj_bir_tm "x10",
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))``,
 ``BExp_BinPred
      BIExp_Equal
      (BExp_Load
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "x10" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 xv))``
];

Definition bspec_incr_mem_pre_def:
  bspec_incr_mem_pre (x:word64) (xv:word64) : bir_exp_t =
   ^bspec_incr_mem_pre_tm
End

Definition bspec_incr_mem_post_def:
 bspec_incr_mem_post (x:word64) (xv:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 x))
     BEnd_LittleEndian Bit64)
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 xv)) (BExp_Const (Imm64 1w)))
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem incr_mem_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_incr_mem_pre pre_x10 pre_x10_mem_deref)
  (bspec_incr_mem_pre pre_x10 pre_x10_mem_deref)
Proof
 cheat
QED

Theorem incr_mem_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
  (riscv_incr_mem_post pre_x10 pre_x10_mem_deref)
  (\l. bspec_incr_mem_post pre_x10 pre_x10_mem_deref) ls
Proof
 cheat
QED

val _ = export_theory ();
