open HolKernel boolLib Parse bossLib;

open kernel_trap_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "kernel_trap_spec_bir";

(* Each call translates a RISC-V condition riscv_<c> to BIR: it defines
   <c>_bir and saves the relation theorem riscv_<c>_to_bir_thm
   (see riscv_bir_condLib.sig) *)

(* trap_entry contract *)

val _ = riscv_pre_to_bir riscv_kernel_trap_entry_pre_def;

val _ = riscv_post_to_bir riscv_kernel_trap_entry_post_def;

(* trap_return contract *)

val _ = riscv_pre_to_bir riscv_kernel_trap_return_pre_def;

val _ = riscv_post_to_bir riscv_kernel_trap_return_post_def;

val _ = export_theory ();
