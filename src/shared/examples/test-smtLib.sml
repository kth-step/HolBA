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
