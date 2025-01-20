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

Definition trap_entry_init_addr_def:
 trap_entry_init_addr : word64 = 0x800000e0w
End

Definition trap_entry_end_addr_def:
 trap_entry_end_addr : word64 = 0x80000190w
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

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

(*
Definition bspec_kernel_trap_pre_def:
 bspec_kernel_trap_pre (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))
End

Definition bspec_kernel_trap_post_def:
 bspec_kernel_trap_post (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x10)) (BExp_Const (Imm64 1w)))
End
*)

(* -------------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* -------------------------------------- *)

val _ = export_theory ();
