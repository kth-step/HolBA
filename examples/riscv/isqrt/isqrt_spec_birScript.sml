open HolKernel boolLib Parse bossLib;

open isqrt_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "isqrt_spec_bir";

(* Each call translates a RISC-V condition riscv_<c> to BIR: it defines
   bspec_<c> and saves the relation theorem riscv_<c>_to_bir_thm
   (see riscv_bir_condLib.sig) *)

(* before loop contract *)

val _ = riscv_pre_to_bir riscv_isqrt_pre_1_def;

val _ = riscv_post_to_bir riscv_isqrt_post_1_def;

(* loop body contract *)

val _ = riscv_pre_to_bir riscv_isqrt_pre_2_def;

val _ = riscv_post_to_bir riscv_isqrt_post_2_def;

(* loop branch contract *)

val _ = riscv_pre_to_bir riscv_isqrt_pre_3_def;

val _ = riscv_post_cases_to_bir riscv_isqrt_post_3_def
  [riscv_isqrt_post_3_loop_def, riscv_isqrt_post_3_ret_def];

val _ = export_theory ();
