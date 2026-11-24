open HolKernel boolLib Parse bossLib;

open bir_predLib;

open bir_riscv_backlifterTheory;

val _ = new_theory "modexp_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition modexp_init_addr_def:
 modexp_init_addr : word64 = 0x28w
End

Definition modexp_end_addr_def:
 modexp_end_addr : word64 = 0x24w
End

(* The M-mode contract that the lifted blocks assert *)
Definition bspec_modexp_pre_def:
bspec_modexp_pre (x:word64) : bir_exp_t =
 ^(rhs (concl bir_riscv_mmode_pre_def))
End

val _ = export_theory ();
