open HolKernel boolLib Parse bossLib;

open bir_predLib;

open bir_riscv_backlifterTheory;

val _ = new_theory "motor_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition motor_init_addr_def:
 motor_init_addr : word64 = 0x7acw
End

(* 0x674w : indirect jump at first function return *)
(* 0x7c4w : run through half of the functions *)
(* 0x7d4w : run through all functions *)
Definition motor_end_addr_def:
 motor_end_addr : word64 = 0x7c4w
End

(* The M-mode contract that the lifted blocks assert, and the conditions
 * on the memory accesses *)
Definition bspec_motor_pre_def:
bspec_motor_pre (x:word64) : bir_exp_t =
 BExp_BinExp BIExp_And
  ^(rhs (concl bir_riscv_mmode_pre_def))
  (BExp_BinExp BIExp_And
    (BExp_BinPred
      BIExp_Equal
      (BExp_Den (BVar "x2" (BType_Imm Bit64)))
      (BExp_Const (Imm64 x)))
    (^(mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x2")))
End

val _ = export_theory ();
