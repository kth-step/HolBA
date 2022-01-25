open HolKernel Parse boolLib bossLib;

open bir_exp_to_wordsLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

(*
(* for debugging the z3 input and output (keep the temporary files) *)
val _ = Library.trace := 5;
*)

val bir_exprs = [
  ("32-bits constant, plus, eq, novar, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 12345w)) (BExp_Const (Imm32 1w)))
        (BExp_Const (Imm32 12346w))``,
    NONE,
    SOME true),
  ("32-bits constant, plus, eq, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 12345w)) (BExp_Const (Imm32 x)))
        (BExp_Const (Imm32 12346w))``,
    SOME [("x", “(1w :word32)”)],
    SOME true),
  ("32-bits constant, plus, eq, unsat",
    ``BExp_BinPred BIExp_Equal
        (BExp_BinExp BIExp_Minus (BExp_Const (Imm32 12345w)) (BExp_Const (Imm32 1w)))
        (BExp_Const (Imm32 12346w))``,
    NONE,
    SOME false),
  ("32-bits constant, right shift, eq, novar, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_BinExp BIExp_RightShift (BExp_Const (Imm32 0xFFw)) (BExp_Const (Imm32 2w)))
        (BExp_Const (Imm32 x))``,
    SOME [("x", “(0x3Fw :word32)”)],
    SOME true),
  ("32-bits constant, left shift, eq, novar, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 0xFFw)) (BExp_Const (Imm32 2w)))
        (BExp_Const (Imm32 x))``,
    SOME [("x", “(0x3FCw :word32)”)],
    SOME true),
  ("32-bits constant, unsigned cast up, eq, novar, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_Cast BIExp_UnsignedCast (BExp_Const (Imm32 0xFFw)) Bit64)
        (BExp_Const (Imm64 x))``,
    SOME [("x", “(0xFFw :word64)”)],
    SOME true),
  ("32-bits constant, unsigned cast down, eq, novar, sat",
    ``BExp_BinPred BIExp_Equal
        (BExp_Cast BIExp_UnsignedCast (BExp_Const (Imm32 0xFFFFw)) Bit8)
        (BExp_Const (Imm8 x))``,
    SOME [("x", “(0xFFw :word8)”)],
    SOME true)
];

fun produce_sat_thm term model =
  let
    val eq_list = List.map (fn (name, tm) => Term [QUOTE name, QUOTE " = ", ANTIQUOTE tm]) model;
    val conj_assign_tm = list_mk_conj eq_list;
    val imp_tm = mk_imp (conj_assign_tm, term);
  in
    prove (imp_tm, SIMP_TAC std_ss [] >> EVAL_TAC)
  end;

val model_eq = option_eq (list_eq (pair_eq (fn (a:string) => fn (b:string) => a=b) identical));

(*
val (name, bir_exp, expected_model_o, expected_sat_o) = List.nth(bir_exprs, 2);
*)

(* Print all BIR expressions as words expressions and check that they are correct. *)
val _ = List.map
  (fn (name, bir_exp, expected_model_o, expected_sat_o) =>
    let
      val word_exp_bool = bir2bool bir_exp;

      val model_o =
        SOME (Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_exp_bool)
        handle _ => NONE;

      val sat_o =
        case (model_o, expected_sat_o) of
            (SOME model, SOME _) =>
              (SOME (produce_sat_thm word_exp_bool model; true)
               handle _ => SOME false)
          | (NONE, SOME _) =>
              (SOME (produce_sat_thm word_exp_bool [("aaaanooovaaarname", “T”)]; true)
               handle _ => SOME false)
          | _ => NONE;

      val correct =
        model_eq expected_model_o model_o andalso
        expected_sat_o = sat_o;

      val _ = print (name ^ ":\n")
      val _ = Hol_pp.print_term word_exp_bool;
      val _ = if correct then () else (
        print "Expected: \n";
        (*Hol_pp.print_term expected;*)
        print "\n";
        raise Fail ("Incorrect result for '" ^ name ^ "'")
        )
      val _ = print "\n"
    in () end) bir_exprs;

