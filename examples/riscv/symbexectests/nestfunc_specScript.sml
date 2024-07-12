open HolKernel boolLib Parse bossLib;

open bir_predLib;

val _ = new_theory "nestfunc_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition nestfunc_init_addr_def:
 nestfunc_init_addr : word64 = 0x678w
End

Definition nestfunc_end_addr_def:
 nestfunc_end_addr : word64 = 0x6c4w
End

Definition bspec_nestfunc_pre_def:
bspec_nestfunc_pre (x:word64) : bir_exp_t =
 BExp_BinExp BIExp_And
  (BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x)))
  (^(mem_addrs_aligned_prog_disj_bir_tm "x2"))
End

val _ = export_theory ();
