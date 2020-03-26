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

fun querysmt q =
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

val result = querysmt q;
*)*)*)*)
end (* local *)

(*
querysmt "(simplify ((_ extract 3 2) #xFC))"

querysmt "(simplify (bvor #x6 #x3))"

querysmt "(display (_ bv20 10))"
*)

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expSyntax bir_immSyntax bir_envSyntax bir_exp_immSyntax bir_exp_memSyntax;
  open bir_bool_expSyntax;
  open bir_valuesSyntax;
  open wordsSyntax;

  val ERR = Feedback.mk_HOL_ERR "bir_smtLib";

in

  fun bvar_to_smtlib_ref bv =
    "birv_" ^ ((fst o dest_BVar_string) bv);

  fun castt_to_smtlib castt = (*
    if is_BIExp_LowCast castt then "CL"
    else if is_BIExp_HighCast castt then "CH"
    else if is_BIExp_SignedCast castt then "CS"
    else if is_BIExp_UnsignedCast castt then "CU"
    else *) raise ERR "castt_to_smtlib"
      ("don't know how to print BIR cast-type: " ^ (term_to_string castt));

  fun bop_to_smtlib bop = (*
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
    else raise ERR "bop_to_smtlib"
      ("don't know how to print BIR bin-op: " ^ (term_to_string bop));

  fun bpredop_to_smtlib bpredop =
    if is_BIExp_Equal bpredop then "="
(*
    else if is_BIExp_NotEqual bpredop then "<>"
    else if is_BIExp_LessThan bpredop then "<"
    else if is_BIExp_SignedLessThan bpredop then "s<"
    else if is_BIExp_LessOrEqual bpredop then "<="
    else if is_BIExp_SignedLessOrEqual bpredop then "s<="
*)
    else raise ERR "bpredop_to_smtlib"
      ("don't know how to print BIR bin-pred-op: " ^ (term_to_string bpredop));

  fun uop_to_smtlib uop = (*
    if is_BIExp_ChangeSign uop then "-"
    else if is_BIExp_Not uop then "!"
    else if is_BIExp_CLZ uop then "($CLZ)"
    else if is_BIExp_CLS uop then "($CLS)"
    else *) raise ERR "uop_to_smtlib"
      ("don't know how to print BIR unary-op: " ^ (term_to_string uop));

  fun endi_to_smtlib endi = (*
    if is_BEnd_BigEndian endi then "B"
    else if is_BEnd_LittleEndian endi then "L"
    else if is_BEnd_NoEndian endi then "N"
    else *) raise ERR "endi_to_smtlib"
      ("don't know how to print endianness: " ^ (term_to_string endi));

fun bexp_to_smtlib bvars exp =
    let
      val _ = ();
    in
      if is_BExp_Const exp then
        let
          val (sz, wv) = (gen_dest_Imm o dest_BExp_Const) exp;
          val vstr =
            if is_word_literal wv then
              (Arbnum.toString o dest_word_literal) wv
            else raise ERR "bexp_to_smtlib" ("can only handle word literals: " ^ (term_to_string exp));
        in
          (bvars, "(_ bv" ^ vstr ^ " " ^ (Int.toString sz) ^ ")")
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
          val bv = dest_BExp_Den exp;
        in
          (Redblackset.add(bvars, bv), bvar_to_smtlib_ref bv)
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
          val uopstr = uop_to_smtlib uop;
          val (bvars, str) = bexp_to_smtlib bvars exp;
        in
          (bvars, "(" ^ uopstr ^ " " ^ str ^ ")")
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_smtlib bop;
          val (bvars1, str1) = bexp_to_smtlib bvars  exp1;
          val (bvars2, str2) = bexp_to_smtlib bvars1 exp2;
        in
          (bvars2, "(" ^ bopstr ^ " " ^ str1 ^ " " ^ str2 ^ ")")
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_smtlib bpredop;
          val (bvars1, str1) = bexp_to_smtlib bvars  exp1;
          val (bvars2, str2) = bexp_to_smtlib bvars1 exp2;
        in
          (bvars2, "(" ^ bpredopstr ^ " " ^ str1 ^ " " ^ str2 ^ ")")
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
        raise (ERR "bir_to_smtlib" ("don't know BIR expression: '" ^ term_to_string exp ^ "'"))
    end;


  fun bvar_to_smtlib_decl bv =
    let
      val sid = bvar_to_smtlib_ref bv;
      val btype = (snd o dest_BVar_string) bv;
      val stype =
        if      is_BType_Imm1  btype then
          "(_ BitVec 1)"
        else if is_BType_Imm8  btype then
          "(_ BitVec 8)"
        else if is_BType_Imm16 btype then
          "(_ BitVec 16)"
        else if is_BType_Imm32 btype then
          "(_ BitVec 32)"
        else if is_BType_Imm64 btype then
          "(_ BitVec 64)"
        else raise ERR "bvar_to_smtlib_decl"
                       ("don't know how to convert BIR type: " ^ (term_to_string btype));
    in
      "(declare-const " ^ sid ^ " " ^ stype ^ ")"
    end;


val t = ``(BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 3w)))``;
val t = ``(BExp_BinPred BIExp_Equal
             ^t
             (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 4w)))
          )``;

val bvars = Redblackset.empty Term.compare;
val (bvars, str) = bexp_to_smtlib bvars t;
(*
val bv = (hd o Redblackset.listItems) bvars;
*)
val bvardecl = Redblackset.foldr (fn (bv, str) => str ^ (
        bvar_to_smtlib_decl bv
      ) ^ "\n") "" bvars;

val q = bvardecl ^ "\n" ^ "(assert " ^ str ^ ")\n" ^ "(check-sat)\n";
val result = querysmt q;

end (* local *)

end (* struct *)
