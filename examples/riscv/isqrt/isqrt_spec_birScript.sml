open HolKernel boolLib Parse bossLib;

open isqrt_spec_riscvTheory;

open riscv_bir_condLib;

val _ = new_theory "isqrt_spec_bir";

(* -------------------------------------------------- *)
(* BSPEC contracts, translated from RISC-V conditions *)
(* -------------------------------------------------- *)

(* before loop contract *)

val (_, isqrt_riscv_pre_1_imp_bspec_pre_1) =
  riscv_pre_to_bir riscv_isqrt_pre_1_def;

val (_, isqrt_riscv_post_1_imp_bspec_post_1) =
  riscv_post_to_bir riscv_isqrt_post_1_def;

Theorem isqrt_riscv_pre_1_imp_bspec_pre_1_thm =
  isqrt_riscv_pre_1_imp_bspec_pre_1

Theorem isqrt_riscv_post_1_imp_bspec_post_1_thm =
  isqrt_riscv_post_1_imp_bspec_post_1

(* loop body contract *)

val (_, isqrt_riscv_pre_2_imp_bspec_pre_2) =
  riscv_pre_to_bir riscv_isqrt_pre_2_def;

val (_, isqrt_riscv_post_2_imp_bspec_post_2) =
  riscv_post_to_bir riscv_isqrt_post_2_def;

Theorem isqrt_riscv_pre_2_imp_bspec_pre_2_thm =
  isqrt_riscv_pre_2_imp_bspec_pre_2

Theorem isqrt_riscv_post_2_imp_bspec_post_2_thm =
  isqrt_riscv_post_2_imp_bspec_post_2

(* loop branch contract *)

val (_, isqrt_riscv_pre_3_imp_bspec_pre_3) =
  riscv_pre_to_bir riscv_isqrt_pre_3_def;

val (_, isqrt_riscv_post_3_imp_bspec_post_3) =
  riscv_post_cases_to_bir riscv_isqrt_post_3_def
    [riscv_isqrt_post_3_loop_def, riscv_isqrt_post_3_ret_def];

Theorem isqrt_riscv_pre_3_imp_bspec_pre_3_thm =
  isqrt_riscv_pre_3_imp_bspec_pre_3

Theorem isqrt_riscv_post_3_imp_bspec_post_3_thm =
  isqrt_riscv_post_3_imp_bspec_post_3

val _ = export_theory ();
