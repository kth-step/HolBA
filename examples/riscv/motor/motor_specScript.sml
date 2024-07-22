open HolKernel boolLib Parse bossLib;

open bir_predLib;

val _ = new_theory "motor_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition motor_init_addr_def:
 motor_init_addr : word64 = 0x7acw
End

(* 0x7d4w : run through all functions *)
(* 0x674w : indirect jump at first function return *)
Definition motor_end_addr_def:
 motor_end_addr : word64 = 0x7c4w
End

Definition bspec_motor_pre_def:
bspec_motor_pre (x:word64) : bir_exp_t =
 BExp_BinExp BIExp_And
  (BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x)))
  (^(mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x2"))
End

val _ = export_theory ();
