open HolKernel boolLib Parse bossLib;

open kernel_trap_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "kernel_trap_spec_bir";

(* ---------------------------------------------------- *)
(* BSPEC trap_entry contract, translated from RISC-V     *)
(* ---------------------------------------------------- *)

(* Defines bspec_kernel_trap_entry_pre and bspec_kernel_trap_entry_post *)

val (_, kernel_trap_entry_riscv_pre_imp_bspec_pre) =
  riscv_pre_to_bir riscv_kernel_trap_entry_pre_def;

val (_, kernel_trap_entry_riscv_post_imp_bspec_post) =
  riscv_post_to_bir riscv_kernel_trap_entry_post_def;

(* ---------------------------------------------------- *)
(* BSPEC trap_return contract, translated from RISC-V    *)
(* ---------------------------------------------------- *)

(* Defines bspec_kernel_trap_return_pre and bspec_kernel_trap_return_post *)

val (_, kernel_trap_return_riscv_pre_imp_bspec_pre) =
  riscv_pre_to_bir riscv_kernel_trap_return_pre_def;

val (_, kernel_trap_return_riscv_post_imp_bspec_post) =
  riscv_post_to_bir riscv_kernel_trap_return_post_def;

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem kernel_trap_entry_riscv_pre_imp_bspec_pre_thm =
  kernel_trap_entry_riscv_pre_imp_bspec_pre

Theorem kernel_trap_entry_riscv_post_imp_bspec_post_thm =
  kernel_trap_entry_riscv_post_imp_bspec_post

Theorem kernel_trap_return_riscv_pre_imp_bspec_pre_thm =
  kernel_trap_return_riscv_pre_imp_bspec_pre

Theorem kernel_trap_return_riscv_post_imp_bspec_post_thm =
  kernel_trap_return_riscv_post_imp_bspec_post

val _ = export_theory ();
