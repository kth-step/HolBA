open HolKernel boolLib Parse bossLib;

open swap_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "swap_spec_bir";

(* -------------------------------------------------- *)
(* BSPEC contract, translated from the RISC-V contract *)
(* -------------------------------------------------- *)

(* Defines bspec_swap_pre and bspec_swap_post *)

val (_, swap_riscv_pre_imp_bspec_pre) = riscv_pre_to_bir riscv_swap_pre_def;

val (_, swap_riscv_post_imp_bspec_post) =
  riscv_post_to_bir riscv_swap_post_def;

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem swap_riscv_pre_imp_bspec_pre_thm = swap_riscv_pre_imp_bspec_pre

Theorem swap_riscv_post_imp_bspec_post_thm = swap_riscv_post_imp_bspec_post

val _ = export_theory ();
