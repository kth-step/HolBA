structure bir_pred_cm0Lib =
struct

open Abbrev;

local
  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
in

(*
local
 val prog_addr_max_tm = ``0x20000w:word32``;
 val mem_addr_bound_tm = ``0x80000000w:word32``;
in
 val mem_params_standard = (prog_addr_max_tm, mem_addr_bound_tm);
end
*)

fun mem_addrs_stack_disj_bir_tm sp other =
``BExp_BinPred BIExp_LessThan
     ^(other) (^(sp))``;

fun mem_load_sp_tm sp idx =
``
  (BExp_Load
                                  (BExp_Den
                                     (BVar "MEM" (BType_Mem Bit32 Bit8)))
                                  (BExp_BinExp BIExp_Plus (^sp)
    ^(bconst32 (idx)))
                                  BEnd_LittleEndian Bit32)``;

(*
val (rn1, sz1) = ("x14", (4*4*256));
val (rn2, sz2) = ("x12", (4*4));
*)
fun mem_area_disj_reg_bir_tm (bvrn1, sz1) (bvrn2, sz2) =
let
  val bprnsz1 = bplus (bvrn1, bconst32 (sz1 - 1));
  val bprnsz2 = bplus (bvrn2, bconst32 (sz2 - 1));
in
  bandl (
     (if sz1 = 1 then [] else [blt (bvrn1, bprnsz1)])
    @(if sz2 = 1 then [] else [blt (bvrn2, bprnsz2)])
    @[borl [
      blt (bprnsz1, bvrn2),
      blt (bprnsz2, bvrn1)
    ]]
  )
end;

fun mem_addrs_prog_disj_bir_tm (prog_addr_max_tm, mem_addr_bound_tm) exp_tm = ``BExp_BinExp BIExp_And
 (BExp_BinPred BIExp_LessOrEqual
  (BExp_Const (Imm32 ^prog_addr_max_tm))
  ^(exp_tm))
 (BExp_BinPred BIExp_LessThan
  ^(exp_tm)
  (BExp_Const (Imm32 ^mem_addr_bound_tm)))``;

fun mem_addrs_aligned_prog_disj_bir_tm mem_params exp_tm = ``BExp_BinExp BIExp_And
  (BExp_Aligned Bit32 2 ^(exp_tm))
  (^(mem_addrs_prog_disj_bir_tm mem_params exp_tm))``;

fun mem_addrs_aligned_prog_disj_riscv_tm (prog_addr_max_tm, mem_addr_bound_tm) vn =
 let
   val var_tm = mk_var (vn, wordsSyntax.mk_int_word_type 32)
 in
  ``^var_tm && 7w = 0w /\ ^prog_addr_max_tm <=+ ^var_tm /\ ^var_tm <+ ^mem_addr_bound_tm``
 end;

fun pre_vals_reg_bir_tm rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit32)))
      (BExp_Const (Imm32 `@ [QUOTE fv] @`)))
`);

fun pre_vals_mem_reg_bir_tm mn rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Load
        (BExp_Den (BVar ^(stringSyntax.fromMLstring mn) (BType_Mem Bit32 Bit8)))
        (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit32)))
        BEnd_LittleEndian Bit32)
      (BExp_Const (Imm32 `@ [QUOTE fv] @`)))
`);

fun pre_vals_bir_tm mn rn fvr fvmd =
 band (pre_vals_reg_bir_tm rn fvr, pre_vals_mem_reg_bir_tm mn rn fvmd);

end (* local *)

end (* structure *)

