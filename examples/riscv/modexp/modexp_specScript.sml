open HolKernel boolLib Parse bossLib;

open bir_predLib;

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

Definition bspec_modexp_pre_def:
bspec_modexp_pre (x:word64) : bir_exp_t =
 (BExp_Const (Imm1 1w))
End

val _ = export_theory ();
