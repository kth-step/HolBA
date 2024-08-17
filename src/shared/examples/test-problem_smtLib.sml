open HolKernel Parse boolLib bossLib;
open bslSyntax;

open bir_smtLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

(* TODO: generalize this for 32 and 64bit memory, also for all value sizes of 8/16/32/64 *)
(* TODO: run this on different z3 versions and see what happens *)
(* TODO: then try what happens when the export works differently: prelude/direct-concat-extract/extract-multiple-asserts-abbreviations *)

val MEM_tm = ``(BVar "sy_MEM8" (BType_Mem Bit64 Bit8))``;
val MEM_e_tm = ``(BExp_Den ^MEM_tm)``;
val ad0_deref_tm = ``BExp_Const (Imm64 pre_x10_deref)``;
val ad1_deref_tm = ``BExp_Const (Imm64 pre_x11_deref)``;
val ad0_tm = ``BExp_Den (BVar "sy_x10" (BType_Imm Bit64))``;
val ad1_tm = ``BExp_Den (BVar "sy_x11" (BType_Imm Bit64))``;
val conds_tms = [``BExp_BinPred BIExp_Equal
                             (BExp_BinExp BIExp_And
                                (^ad0_tm)
                                (BExp_Const (Imm64 7w)))
                             (BExp_Const (Imm64 0w))``,
             ``BExp_BinPred BIExp_Equal
                                (BExp_BinExp BIExp_And
                                   (^ad1_tm)
                                   (BExp_Const (Imm64 7w)))
                                (BExp_Const (Imm64 0w))``,
             ``BExp_BinPred BIExp_Equal
                                   (BExp_Load
                                      (^MEM_e_tm)
                                      (^ad0_tm)
                                      BEnd_LittleEndian Bit64)
                                   (^ad0_deref_tm)``,
             ``BExp_BinPred BIExp_Equal
                                      (BExp_Load
                                         (^MEM_e_tm)
                                         (^ad1_tm)
                                         BEnd_LittleEndian Bit64)
                                      (^ad1_deref_tm)``];

val conds = [];
val vars = Redblackset.empty smtlib_vars_compare;

val (conds,vars) = foldr (fn (cond_tm,(conds,vars)) =>
  let
    val (conds, vars, str) = bexp_to_smtlib conds vars cond_tm;
  in
    (str::conds, vars)
  end) (conds,vars) conds_tms;

(*
(assert (= (bvand ad0 (_ bv1 64)) (_ bv0 64)))
(assert (= (bvand ad1 (_ bv1 64)) (_ bv0 64)))
(assert (= (loadfun_64_8_16 M ad0) ad0_deref))
(assert (= (loadfun_64_8_16 M ad1) ad1_deref))
*)

val M_tm = ``BExp_Store
                        (BExp_Store
                           (^MEM_e_tm)
                           (^ad0_tm)
                           BEnd_LittleEndian
                           (^ad1_deref_tm))
                        (^ad1_tm)
                        BEnd_LittleEndian
                        (^ad0_deref_tm)``;

val query_tm = bnot (band (beq (bload M_tm ad0_tm ``BEnd_LittleEndian`` ``Bit64``, ad1_deref_tm),
                           beq (bload M_tm ad1_tm ``BEnd_LittleEndian`` ``Bit64``, ad0_deref_tm)));

val (conds, vars, str) = bexp_to_smtlib conds vars query_tm;

(*
(assert (not (and 
  (= (loadfun_64_8_16 (storefun_64_8_16 (storefun_64_8_16 M ad0 ad1_deref) ad1 ad0_deref) ad0) ad1_deref)
  (= (loadfun_64_8_16 (storefun_64_8_16 (storefun_64_8_16 M ad0 ad1_deref) ad1 ad0_deref) ad1) ad0_deref))))
*)

val _ = print "Testing with z3\n";

(* check with timeout, because these test cases might cause excessive runtime or non-termination *)
val result = querysmt_wtimeout (SOME 4000) vars ([str]@conds);

val _ = if result = BirSmtUnsat then () else
        raise Fail "Unexpected result. Should be unsat.";

