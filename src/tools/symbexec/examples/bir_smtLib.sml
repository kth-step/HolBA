structure bir_smtLib =
struct

local

open bir_scamv_helpersLib;

(* directory creation helper *)
  fun makedir makepath path =
    let
      val r = OS.Process.system ("mkdir " ^ (if makepath then "-p " else "") ^ path);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "makedir" ("couldn't create the following directory: " ^ path)
              else
                ();
    in
      ()
    end;

fun get_tempfile prefix =
  let
    val tempdir = "tempdir";
    val _ = makedir true tempdir;
    val date = Date.fromTimeLocal (Time.now ());
    val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
  in
    tempdir ^ "/" ^ prefix ^ "_" ^ datestr
  end;

fun writeToFile str file_name =
  let
    val outstream = TextIO.openOut file_name;
    val _ = TextIO.output (outstream, str) before TextIO.closeOut outstream;
  in
    () 
  end;


in

datatype bir_smt_result =
    BirSmtSat
  | BirSmtUnsat
  | BirSmtUnknown;

fun querysmt_raw q =
  let
    val tempfile = get_tempfile "smtquery";
    val _ = writeToFile q tempfile;

    val out = get_exec_output ("z3 " ^ tempfile);
  in
    if out = "sat\n" then
      BirSmtSat
    else if out = "unsat\n" then
      BirSmtUnsat
    else if out = "unknown\n" then
      BirSmtUnknown
    else
      (print "\n============================\n";
       print out;
       print "\n============================\n";
       raise ERR "querysmt" "unknown output from z3")
  end;

(* https://rise4fun.com/z3/tutorial *)
(*
val q = "(declare-const a Int)\n" ^
        "(declare-fun f (Int Bool) Int)\n" ^
        "(assert (> a 10))\n" ^
        "(assert (< (f a true) 100))\n" ^
        "(check-sat)\n";

val q = "(declare-const a Int)\n" ^
        "(declare-fun f (Int Bool) Int)\n" ^
        "(assert (> a 10))\n" ^
        "(assert (< (f a true) 100))\n" ^
        "(assert (>= (f a true) 100))\n" ^
        "(check-sat)\n";

val q = "(declare-const a Int)\n" ^
        "(declare-const b Real)\n" ^
        "(declare-const c Real)\n" ^
        "(assert (> (* a a) 3))\n" ^
        "(assert (= (+ (* b b b) (* b c)) 3.0))\n" ^
        "(check-sat)\n";

val q = "(echo \"Z3 does not always find solutions to non-linear problems\")\n";

val q = "(check-sat)\n";

val result = querysmt_raw q;
*)*)*)*)


datatype bir_smt_type =
    SMTTY_Bool
  | SMTTY_BV8
  | SMTTY_BV16
  | SMTTY_BV32
  | SMTTY_BV64;

fun smt_type_to_smtlib SMTTY_Bool = "Bool"
  | smt_type_to_smtlib SMTTY_BV8  = "(_ BitVec 8)"
  | smt_type_to_smtlib SMTTY_BV16 = "(_ BitVec 16)"
  | smt_type_to_smtlib SMTTY_BV32 = "(_ BitVec 32)"
  | smt_type_to_smtlib SMTTY_BV64 = "(_ BitVec 64)";

fun smt_type_is_bv SMTTY_Bool = false
  | smt_type_is_bv SMTTY_BV8  = true
  | smt_type_is_bv SMTTY_BV16 = true
  | smt_type_is_bv SMTTY_BV32 = true
  | smt_type_is_bv SMTTY_BV64 = true;

fun smt_vars_to_smtlib vars =
  Redblackset.foldr (fn ((vn, vty), str) => str ^ (
        "(declare-const " ^ vn ^ " " ^ (smt_type_to_smtlib vty) ^ ")"
      ) ^ "\n") "" vars;

fun querysmt vars asserts =
  if List.exists (fn (_,qt) => qt <> SMTTY_Bool) asserts then
    raise ERR "querysmt" "don't know how to handle expression type in assert"
  else
    let
      val decls = smt_vars_to_smtlib vars;
      val asserts_str =
        List.foldr (fn ((q,_), str) => str ^ (
          "(assert " ^ q ^ ")\n"
        )) "" asserts;
    in
      querysmt_raw (decls ^ "\n" ^ asserts_str ^ "(check-sat)\n")
    end;

fun smtlib_vars_compare ((an, aty),(bn, bty)) =
  if an = bn then
    String.compare (smt_type_to_smtlib aty, smt_type_to_smtlib bty)
  else
    String.compare (an, bn);
  
(*
querysmt (Redblackset.fromList smtlib_vars_compare [("x", SMTTY_BV8)])
         [("(= x #xFF)", SMTTY_Bool)]

querysmt (Redblackset.fromList smtlib_vars_compare [("x", SMTTY_BV8)])
         [("(= x #xFF)", SMTTY_Bool), ("(= x #xAA)", SMTTY_Bool)]
*)

end (* local *)

(*
querysmt_raw "(simplify ((_ extract 3 2) #xFC))"

querysmt_raw "(simplify (bvor #x6 #x3))"

querysmt_raw "(display (_ bv20 16))"
*)

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expSyntax bir_immSyntax bir_envSyntax bir_exp_immSyntax bir_exp_memSyntax;
  open bir_bool_expSyntax;
  open bir_valuesSyntax;
  open wordsSyntax;

  val ERR = Feedback.mk_HOL_ERR "bir_smtLib";

fun problem_gen fname t msg = 
  raise ERR fname (msg ^ (term_to_string t));

in

  fun bvar_to_smtlib_ref bv =
    "birv_" ^ ((fst o dest_BVar_string) bv);

  fun bvar_to_smtlib_type bv =
    let
      val btype = (snd o dest_BVar_string) bv;
    in
        if      is_BType_Imm1  btype then
          SMTTY_Bool
        else if is_BType_Imm8  btype then
          SMTTY_BV8
        else if is_BType_Imm16 btype then
          SMTTY_BV16
        else if is_BType_Imm32 btype then
          SMTTY_BV32
        else if is_BType_Imm64 btype then
          SMTTY_BV64
        else problem_gen "bvar_to_smtlib_type" btype "don't know how to convert BIR type: "
    end;



  fun castt_to_smtlib sty castt = (*
    if is_BIExp_LowCast castt then "CL"
    else if is_BIExp_HighCast castt then "CH"
    else if is_BIExp_SignedCast castt then "CS"
    else if is_BIExp_UnsignedCast castt then "CU"
    else *) problem_gen "castt_to_smtlib" castt "don't know how to print BIR cast-type: ";

  fun bop_to_smtlib sty bop = (*
    if is_BIExp_And bop then "&"
    else if is_BIExp_Or bop then "|"
    else if is_BIExp_Xor bop then "^"
    else *) if is_BIExp_Plus bop then "bvadd"
(*
    else if is_BIExp_Minus bop then "-"
    else if is_BIExp_Mult bop then "*"
    else if is_BIExp_Div bop then "/"
    else if is_BIExp_SignedDiv bop then "s/"
    else if is_BIExp_Mod bop then "%"
    else if is_BIExp_SignedMod bop then "s<<"
    else if is_BIExp_LeftShift bop then "<<"
    else if is_BIExp_RightShift bop then ">>"
    else if is_BIExp_SignedRightShift bop then "s>>"
*)
    else problem_gen "bop_to_smtlib" bop "don't know how to print BIR bin-op: ";

  fun bpredop_to_smtlib sty bpredop =
    if is_BIExp_Equal bpredop then "="
(*
    else if is_BIExp_NotEqual bpredop then "<>"
    else if is_BIExp_LessThan bpredop then "<"
    else if is_BIExp_SignedLessThan bpredop then "s<"
    else if is_BIExp_LessOrEqual bpredop then "<="
    else if is_BIExp_SignedLessOrEqual bpredop then "s<="
*)
    else raise problem_gen "bpredop_to_smtlib" bpredop "don't know how to print BIR bin-pred-op: ";

  fun uop_to_smtlib sty uop = (*
    if is_BIExp_ChangeSign uop then "-"
    else if is_BIExp_Not uop then "!"
    else if is_BIExp_CLZ uop then "($CLZ)"
    else if is_BIExp_CLS uop then "($CLS)"
    else *) problem_gen "uop_to_smtlib" uop "don't know how to print BIR unary-op: ";

  fun endi_to_smtlib sty endi = (*
    if is_BEnd_BigEndian endi then "B"
    else if is_BEnd_LittleEndian endi then "L"
    else if is_BEnd_NoEndian endi then "N"
    else *) problem_gen "endi_to_smtlib" endi "don't know how to print endianness: ";

fun bexp_to_smtlib vars exp =
    let
      fun problem exp msg = problem_gen "bexp_to_smtlib" exp msg;

      fun smtlib_wrap_to_bool   str = "(= #b1 " ^ str ^ ")";
      fun smtlib_wrap_from_bool str = "(ite " ^ str ^ " #b1 #b0)";
    in
      if is_BExp_Const exp then
        let
          val (sz, wv) = (gen_dest_Imm o dest_BExp_Const) exp;
          val vstr =
            if is_word_literal wv then
              (Arbnum.toString o dest_word_literal) wv
            else problem exp "can only handle word literals: ";
        in
          if sz = 1 then
            if Arbnumcore.mod(((dest_word_literal) wv), Arbnumcore.fromInt 2)
               = Arbnumcore.fromInt 1 then
              (vars, ("true", SMTTY_Bool))
            else
              (vars, ("false", SMTTY_Bool))
          else
            (vars, ("(_ bv" ^ vstr ^ " " ^ (Int.toString sz) ^ ")",
               case sz of
                  8  => SMTTY_BV8
                | 16 => SMTTY_BV16
                | 32 => SMTTY_BV32
                | 64 => SMTTY_BV64
                | _  => raise ERR "bexp_to_smtlib" "..."))
        end

(*
      else if is_BExp_MemConst exp then
        let
          val (aty, vty, mmap) = (dest_BExp_MemConst) exp;
          val aty_str = (Int.toString o size_of_bir_immtype_t) aty;
          val vty_str = (Int.toString o size_of_bir_immtype_t) vty;
        in
          ((xf "(MEM:") cf (xf aty_str) cf (xf ":") cf (xf vty_str) cf (xf (":{" ^ (term_to_string mmap) ^ "})")))
        end
*)

      else if is_BExp_Den exp then
        let
          val bv    = dest_BExp_Den exp;
          val sname = bvar_to_smtlib_ref  bv;
          val stype = bvar_to_smtlib_type bv;
          val var   = (sname, stype);
        in
          (Redblackset.add(vars, var), var)
        end

(*
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_smtlib castt;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ((xf "(") cf (ef exp) cf (xf ":") cf (xf casttstr) cf (xf szstr) cf (xf ")"))
        end
*)

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val (bvars, (str, sty)) = bexp_to_smtlib vars exp;
          val uopstr = uop_to_smtlib sty uop;
        in
          (vars, ("(" ^ uopstr ^ " " ^ str ^ ")", sty))
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val (vars1, (str1, sty1)) = bexp_to_smtlib vars  exp1;
          val (vars2, (str2, sty2)) = bexp_to_smtlib vars1 exp2;
          val _ = if sty1 = sty2 then () else
                  problem exp "binary operator needs same type for both sides: ";
          val bopstr = bop_to_smtlib sty1 bop;
        in
          (vars2, ("(" ^ bopstr ^ " " ^ str1 ^ " " ^ str2 ^ ")", sty1))
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val (vars1, (str1, sty1)) = bexp_to_smtlib vars  exp1;
          val (vars2, (str2, sty2)) = bexp_to_smtlib vars1 exp2;
          val _ = if sty1 = sty2 then () else
                  problem exp "binary predicate operator needs same type for both sides: ";
          val bpredopstr = bpredop_to_smtlib sty1 bpredop;
        in
          (vars2, ("(" ^ bpredopstr ^ " " ^ str1 ^ " " ^ str2 ^ ")", SMTTY_Bool))
        end

(*
      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          ((xf "(") cf (ef exp1) cf (xf " = ") cf (ef exp2) cf (xf ")"))
        end
*)

(*
      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          ((xf "(if ") cf (ef expc) cf (xf " then ") cf (ef expt) cf (xf " else ") cf (ef expf) cf (xf ")"))
        end
*)

(*
      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_smtlib endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ((xf "(") cf (ef expm) cf (xf ":") cf (xf endistr) cf (xf szstr) cf (xf "[") cf (ef expad) cf (xf "])"))
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_smtlib endi;
        in
          ((xf "(") cf (ef expm) cf (xf ":") cf (xf endistr) cf (xf "[") cf (ef expad) cf (xf "] = ") cf (ef expv) cf (xf ")"))
        end
*)

(*
      else if is_bir_exp_imp exp then
        let
          val (bir_lhs, bir_rhs) = dest_bir_exp_imp exp
        in
          ((xf "(") cf (ef bir_lhs) cf (xf "==>") cf (ef bir_rhs) cf (xf ")"))
        end
*)
      else
        problem exp "don't know BIR expression: "
    end;


val exp = ``BExp_Const (Imm64 3w)``
val exp = ``BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64))``
val exp = ``BExp_Den (BVar "fr_0_Z" (BType_Imm Bit1))``

val t = ``(BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 3w)))``;
val exp = ``(BExp_BinPred BIExp_Equal
             ^t
             (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 4w)))
          )``;

val vars_empty = Redblackset.empty smtlib_vars_compare;
val (vars, str) = bexp_to_smtlib vars_empty exp;
(*
val vars = vars_empty;
val varlist = Redblackset.listItems vars;
*)

val result = querysmt vars [str];

end (* local *)

end (* struct *)
