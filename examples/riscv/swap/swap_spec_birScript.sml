open HolKernel boolLib Parse bossLib;

open swap_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "swap_spec_bir";

(* Each call translates a RISC-V condition riscv_<c> to BIR: it defines
   bspec_<c> and saves the relation theorem riscv_<c>_to_bir_thm
   (see riscv_bir_condLib.sig) *)

val _ = riscv_pre_to_bir riscv_swap_pre_def;

val _ = riscv_post_to_bir riscv_swap_post_def;

val _ = export_theory ();
