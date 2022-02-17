open HolKernel Parse boolLib bossLib;
open bslSyntax;

open bir_smtLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

val _ = print "Building expressions\n";

val exp = ``BExp_Const (Imm64 3w)``
val exp = ``BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64))``
val exp = ``BExp_Den (BVar "fr_0_Z" (BType_Imm Bit1))``

val t = ``(BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 3w)))``;
val exp = ``(BExp_BinPred BIExp_Equal
             ^t
             (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_1_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 4w)))
          )``;

val conds_init = [("(= birv_fr_0_countw birv_fr_1_countw)", SMTTY_Bool)];


val _ = print "Processing expressions\n";

val vars_empty = Redblackset.empty smtlib_vars_compare;
val (conds, vars, str) = bexp_to_smtlib conds_init vars_empty exp;
(*
val vars = vars_empty;
val varlist = Redblackset.listItems vars;
*)

val _ = print "Testing with z3\n";

val result = querysmt bir_smtLib_z3_prelude vars ([str]@conds);

val _ = if result = BirSmtUnsat then () else
        raise Fail "Unexpected result. Should be unsat.";

val _ = print "Testing the exporting of a few expressions\n";
(* can be tested in z3 with "(simplify expressionhere)" *)
val exporting_exp_testcases = [
  (``BExp_Cast BIExp_UnsignedCast (BExp_Const (Imm16 0x80w)) Bit8``,
   ("((_ extract 7 0) (_ bv128 16))", SMTTY_BV 8)),
  (``BExp_Cast BIExp_UnsignedCast (BExp_Const (Imm8 0x80w)) Bit16``,
   ("(concat #b00000000 (_ bv128 8))", SMTTY_BV 16)),


  (``BExp_Cast BIExp_LowCast (BExp_Const (Imm16 0x80w)) Bit8``,
   ("((_ extract 7 0) (_ bv128 16))", SMTTY_BV 8)),
  (``BExp_Cast BIExp_LowCast (BExp_Const (Imm8 0x80w)) Bit16``,
   ("(concat #b00000000 (_ bv128 8))", SMTTY_BV 16)),


  (``BExp_Cast BIExp_SignedCast (BExp_Const (Imm16 0x80w)) Bit8``,
   ("((_ extract 7 0) (_ bv128 16))", SMTTY_BV 8)),
  (``BExp_Cast BIExp_SignedCast (BExp_Const (Imm8 0x80w)) Bit16``,
   ("((_ sign_extend 8) (_ bv128 8))", SMTTY_BV 16)),
  (``BExp_Cast BIExp_SignedCast (BExp_Const (Imm8 0x7Cw)) Bit16``,
   ("((_ sign_extend 8) (_ bv124 8))", SMTTY_BV 16)),


  (``BExp_Cast BIExp_HighCast (BExp_Const (Imm16 0x4480w)) Bit8``,
   ("((_ extract 15 8) (_ bv17536 16))", SMTTY_BV 8)),
  (``BExp_Cast BIExp_HighCast (BExp_Const (Imm8 0x80w)) Bit16``,
   ("(concat #b00000000 (_ bv128 8))", SMTTY_BV 16)),


  (``BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm1 0x1w)) (BExp_Const (Imm1 0x0w))``,
   ("(=> true false)", SMTTY_Bool))
];

(*
val (exp, expected) = List.nth(exporting_exp_testcases, 0);
*)
val _ = List.map (fn (exp, expected) =>
  let
    val (_, _, res) = bexp_to_smtlib [] vars_empty exp;
    val _ = if res = expected then () else (
            print ("have: ");
            PolyML.print res;
            print ("expecting: ");
            PolyML.print expected;
            raise Fail ("unexpected export: " ^ (term_to_string exp)));
  in () end) exporting_exp_testcases;

(* TODO: need a bunch of test cases that can be automatically checked,
    such that we know what's supposed to come out.
    maybe use EVAL and BIR semantics together with z3's simplify?
*)

(* TODO: addition to the last TODO. with a model importer we can check a full round:
   - send query based on BIR expression
   - get model satisfying BIR expression in terms of bir var assignments
   - evaluate model on BIR expression
*)
