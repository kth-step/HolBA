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
       raise ERR "querysmt_raw" "unknown output from z3")
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

datatype bir_smt_type_bv =
    SMTTY_BV8
  | SMTTY_BV16
  | SMTTY_BV32
  | SMTTY_BV64;

fun smt_type_bv_to_int SMTTY_BV8  = 8
  | smt_type_bv_to_int SMTTY_BV16 = 16
  | smt_type_bv_to_int SMTTY_BV32 = 32
  | smt_type_bv_to_int SMTTY_BV64 = 64;

fun smt_type_bv_from_int 8  = SMTTY_BV8
  | smt_type_bv_from_int 16 = SMTTY_BV16
  | smt_type_bv_from_int 32 = SMTTY_BV32
  | smt_type_bv_from_int 64 = SMTTY_BV64
  | smt_type_bv_from_int i  = raise ERR "smt_type_bv_from_int"
                                        ("unknown bitvector length: " ^ (Int.toString i));

fun smt_type_bv_to_smtlib bvt = "(_ BitVec " ^ (Int.toString (smt_type_bv_to_int bvt)) ^ ")";

datatype bir_smt_type =
    SMTTY_Bool
  | SMTTY_BV of bir_smt_type_bv
  | SMTTY_MEM of (bir_smt_type_bv * bir_smt_type_bv);

fun smt_type_to_smtlib SMTTY_Bool                = "Bool"
  | smt_type_to_smtlib (SMTTY_BV  bvt)           = smt_type_bv_to_smtlib bvt
  | smt_type_to_smtlib (SMTTY_MEM (bvtad, bvtv)) = "(Array " ^ (smt_type_bv_to_smtlib bvtad) ^
                                                         " " ^ (smt_type_bv_to_smtlib bvtv) ^ ")";

fun smt_type_is_bv (SMTTY_BV _) = true
  | smt_type_is_bv _            = false;

fun smt_type_is_bool SMTTY_Bool = true
  | smt_type_is_bool _          = false;

fun smt_type_is_mem (SMTTY_MEM _) = true
  | smt_type_is_mem _             = false;

fun smt_vars_to_smtlib vars =
  Redblackset.foldr (fn ((vn, vty), str) => str ^ (
        "(declare-const " ^ vn ^ " " ^ (smt_type_to_smtlib vty) ^ ")"
      ) ^ "\n") "" vars;

fun querysmt prelude vars asserts =
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
      querysmt_raw (prelude     ^ "\n" ^
                    decls       ^ "\n" ^
                    asserts_str ^ "\n" ^
                    "(check-sat)\n")
    end;

fun smtlib_vars_compare ((an, aty),(bn, bty)) =
  if an = bn then
    String.compare (smt_type_to_smtlib aty, smt_type_to_smtlib bty)
  else
    String.compare (an, bn);
  
(*
querysmt "" (Redblackset.fromList smtlib_vars_compare [("x", SMTTY_BV8)])
         [("(= x #xFF)", SMTTY_Bool)]

querysmt "" (Redblackset.fromList smtlib_vars_compare [("x", SMTTY_BV8)])
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

  fun read_from_file filename =
    let
      val file = TextIO.openIn filename;
      val s    = TextIO.inputAll file before TextIO.closeIn file;
    in
      s
    end;

in

  fun bvar_to_smtlib_ref bv =
    "birv_" ^ ((fst o dest_BVar_string) bv);

  fun bvar_to_smtlib_type bv =
    let
      val btype = (snd o dest_BVar_string) bv;
    in
        if      is_BType_Imm1  btype orelse is_BType_Bool btype then
          SMTTY_Bool
        else if is_BType_Imm8  btype then
          (SMTTY_BV SMTTY_BV8)
        else if is_BType_Imm16 btype then
          (SMTTY_BV SMTTY_BV16)
        else if is_BType_Imm32 btype then
          (SMTTY_BV SMTTY_BV32)
        else if is_BType_Imm64 btype then
          (SMTTY_BV SMTTY_BV64)
        else if is_BType_Mem btype andalso dest_BType_Mem btype = (Bit32_tm, Bit8_tm) then
          (SMTTY_MEM (SMTTY_BV32, SMTTY_BV8))
        else problem_gen "bvar_to_smtlib_type" btype "don't know how to convert BIR type: "
    end;


fun problem_gen_sty fname t sty =
  problem_gen fname t ("don't know how to convert as " ^ (smt_type_to_smtlib sty) ^ ": ");

  fun get_smtlib_type_args probfun args =
    let
      val _   = if length(args) > 0 then () else
                  (print "\n!!!\nneed at least one argument for type unification!!!\n"; probfun ());
      val sty = snd (hd args);
      val _   = if List.all (fn x => snd x = sty) args then () else
                  probfun ();
    in
      sty
    end;

  fun gen_smtlib_expr opstr args sty =
    let
      val argstr = List.foldl (fn ((s,_),str) => str ^ " " ^ s) "" args;
    in
      ("(" ^ opstr ^ argstr ^ ")", sty)
    end;

  fun apply_smtlib_op wrapfun (str, sty) =
     (wrapfun str, sty);

  fun mk_0s i = String.implode (List.tabulate(i,fn _ => #"0"));

(* unsignedcast and lowcast is the same: lowest bits *)
(* highcast: highest bits (shift right and lowest bits) *)
(* signedcast: preserve signed bit (highest bit), take lowest bits otherwise
     - should be sign extension as in SIGN_EXTEND *)
  fun castt_to_smtlib castt str szi_from szi_to =
    if szi_from >= szi_to then
      if is_BIExp_LowCast castt orelse is_BIExp_UnsignedCast castt then
        "((_ extract " ^ (Int.toString (szi_to-1)) ^ " 0) " ^ str ^ ")"
      else if is_BIExp_HighCast castt then
        "((_ extract " ^ (Int.toString (szi_from - 1)) ^
                   " " ^ (Int.toString (szi_from - szi_to)) ^
                  ") " ^ str ^ ")"
(*
    else if is_BIExp_SignedCast castt then "CS"
*)
      else raise ERR "castt_to_smtlib" "don't know about down-SignedCast"
    else
      if is_BIExp_LowCast castt orelse is_BIExp_UnsignedCast castt then
        "(concat #b" ^ (mk_0s (szi_to - szi_from)) ^ " " ^ str ^ ")"
      else if is_BIExp_HighCast castt then
        "(concat " ^ str ^ " #b" ^ (mk_0s (szi_to - szi_from)) ^ ")"
      else raise ERR "castt_to_smtlib" "don't know about up-SignedCast";

  val smtlib_prelude = read_from_file "bir_smtLib.z3_prelude";


  fun bop_to_smtlib sty bop =
    if smt_type_is_bv sty then
      if is_BIExp_And bop then "bvand"
      else if is_BIExp_Or bop then "bvor"
      else if is_BIExp_Xor bop then "bvxor"
      else if is_BIExp_Plus bop then "bvadd"
      else if is_BIExp_Minus bop then "bvsub"
      else if is_BIExp_Mult bop then "bvmul"
      else if is_BIExp_Div bop then "bvudiv"
      else if is_BIExp_SignedDiv bop then "bvsdiv"
(*
      else if is_BIExp_Mod bop then "bvurem" (* TODO: is bvurem the correct correspondence? *)
*)
      else if is_BIExp_SignedMod bop then "bvsmod"
      else if is_BIExp_LeftShift bop then "bvshl"
      else if is_BIExp_RightShift bop then "bvlshr"
      else if is_BIExp_SignedRightShift bop then "bvashr"

      else problem_gen_sty "bop_to_smtlib" bop sty
    else if smt_type_is_bool sty then
      if is_BIExp_And bop then "and"
      else if is_BIExp_Or bop then "or"
      else if is_BIExp_Xor bop then "xor"
      else problem_gen_sty "bop_to_smtlib" bop sty
    else
      problem_gen_sty "bop_to_smtlib" bop sty;

  fun bpredop_to_smtlib probfun bpredop args =
    let
      val sty = get_smtlib_type_args probfun args;
      fun gen_exp opstr = gen_smtlib_expr opstr args SMTTY_Bool;
    in
    (* TODO: BinPred cannot be applied to memories! *)
    if is_BIExp_Equal bpredop then gen_exp "="
    else if is_BIExp_NotEqual bpredop then apply_smtlib_op (fn s => "(not " ^ s ^ ")")
                                                           (gen_exp "=")
    (* TODO: BinPred can be applied to Imm1! *)
    else if smt_type_is_bv sty then
      if is_BIExp_LessThan bpredop then gen_exp "bvult"
      else if is_BIExp_SignedLessThan bpredop then gen_exp "bvslt"
      else if is_BIExp_LessOrEqual bpredop then gen_exp "bvule"
      else if is_BIExp_SignedLessOrEqual bpredop then gen_exp "bvsle"
      else problem_gen_sty "bpredop_to_smtlib" bpredop sty
    else problem_gen_sty "bpredop_to_smtlib" bpredop sty
    end;

  fun uop_to_smtlib uop (str, sty) =
    let fun gen_exp opstr = gen_smtlib_expr opstr [(str, sty)] sty in
    if smt_type_is_bv sty then
      if is_BIExp_ChangeSign uop then gen_exp "bvneg"
      else if is_BIExp_Not uop then gen_exp "bvnot"
(*
      else if is_BIExp_CLZ uop then "($CLZ)"
      else if is_BIExp_CLS uop then "($CLS)"
*)
      else problem_gen_sty "uop_to_smtlib" uop sty
    else if smt_type_is_bool sty then
      if is_BIExp_ChangeSign uop then (str, sty)
      else if is_BIExp_Not uop then gen_exp "not"
(*
      else if is_BIExp_CLZ uop then "($CLZ)"
      else if is_BIExp_CLS uop then "($CLS)"
*)
      else problem_gen_sty "uop_to_smtlib" uop sty
    else
      problem_gen_sty "uop_to_smtlib" uop sty
    end;

  fun endi_to_smtlib sty endi =
(* NOTICE: stick to little endian for now! *)
    if is_BEnd_LittleEndian endi then ()
(*
    else if is_BEnd_BigEndian endi then "B"
    else if is_BEnd_NoEndian endi then "N"
*)
    else problem_gen_sty "endi_to_smtlib" endi sty;

  fun bexp_to_smtlib conds vars exp =
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
              (conds, vars, ("true", SMTTY_Bool))
            else
              (conds, vars, ("false", SMTTY_Bool))
          else
            (conds, vars, ("(_ bv" ^ vstr ^ " " ^ (Int.toString sz) ^ ")",
               SMTTY_BV (smt_type_bv_from_int sz)
               handle HOL_ERR _ => raise ERR "bexp_to_smtlib" "..."))
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
          (conds, Redblackset.add(vars, var), var)
        end

(*
val exp = 
``
BExp_Cast BIExp_UnsignedCast
           (BExp_Cast BIExp_LowCast
              (BExp_Den (BVar "fr_229_R3" (BType_Imm Bit32))) Bit8) Bit32
``
val exp = ``
BExp_Cast BIExp_LowCast
              (BExp_Den (BVar "fr_229_R3" (BType_Imm Bit32))) Bit8
``
*)
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val (conds1, vars1, (stre, stye)) = bexp_to_smtlib conds vars exp;

          val szi = size_of_bir_immtype_t sz;
          val sty = SMTTY_BV (smt_type_bv_from_int szi)
                    handle HOL_ERR _ => raise ERR "bexp_to_smtlib" "...";
          val exp_szi = case stye of
                           SMTTY_BV bvt => smt_type_bv_to_int bvt
                         | _ => problem exp "cast can only be applied to imm (not imm1): ";

          val caststr = castt_to_smtlib castt stre exp_szi szi;

          val castval = (caststr, sty);
        in
          (conds1, vars1, castval)
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val (conds1, vars1, (str, sty)) = bexp_to_smtlib conds vars exp;
          val uopval = uop_to_smtlib uop (str, sty);
        in
          (conds1, vars1, uopval)
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val (conds1, vars1, val1) = bexp_to_smtlib conds  vars  exp1;
          val (conds2, vars2, val2) = bexp_to_smtlib conds1 vars1 exp2;
          val args = [val1, val2];

          val sty =
            get_smtlib_type_args
              (fn () => problem exp "binary operator needs same type for both sides: ")
              args;
          val bopstr = bop_to_smtlib sty bop;
                                         
          val bopval = gen_smtlib_expr bopstr args sty;
        in
          (conds2, vars2, bopval)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val (conds1, vars1, val1) = bexp_to_smtlib conds  vars  exp1;
          val (conds2, vars2, val2) = bexp_to_smtlib conds1 vars1 exp2;
          val args = [val1, val2];

          fun probfun () = problem exp "binary predicate operator needs same type for both sides: ";

          val bpredopval = bpredop_to_smtlib probfun bpredop args;
        in
          (conds2, vars2, bpredopval)
        end

(*
      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          ((xf "(") cf (ef exp1) cf (xf " = ") cf (ef exp2) cf (xf ")"))
        end
*)

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
          val (conds1, vars1, (strc, styc)) = bexp_to_smtlib conds  vars  expc;
          val (conds2, vars2, (strt, styt)) = bexp_to_smtlib conds1 vars1 expt;
          val (conds3, vars3, (strf, styf)) = bexp_to_smtlib conds2 vars2 expf;
          val _ = if smt_type_is_bool styc then () else
                  problem exp "if-then-else needs bool in condition: ";
          val _ = if styt = styf then () else
                  problem exp "if-then-else needs same type for both sides: ";
        in
          (conds3, vars3, ("(ite " ^ strc ^ " " ^ strt ^ " " ^ strf ^ ")", styt))
        end

(*
fun problem _ _ = raise ERR "" "";
val vars_empty = Redblackset.empty smtlib_vars_compare;
val vars = vars_empty;
val conds = [];
val exp = ``
BExp_Load (BExp_Den (BVar "fr_269_MEM" (BType_Mem Bit32 Bit8)))
          (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R7" (BType_Imm Bit32)))
             (BExp_Const (Imm32 4w))) BEnd_LittleEndian Bit32``
*)
      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val (conds1, vars1, valm)  = bexp_to_smtlib conds  vars  expm;
          val (conds2, vars2, valad) = bexp_to_smtlib conds1 vars1 expad;

          val (_,stym) = valm;
          val (_,styad) = valad;
          val _ = endi_to_smtlib stym endi;

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_MEM (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val _ = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";
          val szadi = smt_type_bv_to_int styad_bvt;
          val szci  = smt_type_bv_to_int styc_bvt;

          val szi  = (size_of_bir_immtype_t) sz;
          val styv = SMTTY_BV (smt_type_bv_from_int szi)
                    handle HOL_ERR _ => raise ERR "bexp_to_smtlib" "...";

          (* current restrictions *)
          val _ = if szadi = 32 then () else
                    problem exp "address type other than 32bits cannot be handled currently: ";
          val _ = if szci  =  8 then () else
                    problem exp "cell types other than 8bits cannot be handled currently: ";
          val _ = if szi   =  8 orelse
                     szi   = 32 then () else
                    problem exp "load types other than 8 and 32bits cannot be handled currently: ";

          val z3funname = "loadfun_" ^ (Int.toString szadi) ^
                                 "_" ^ (Int.toString szci) ^
                                 "_" ^ (Int.toString szi);
          val loadval = gen_smtlib_expr z3funname [valm, valad] styv;
        in
          (conds2, vars2, loadval)
        end

(*
val exp = ``
BExp_Store (BExp_Den (BVar "fr_269_MEM" (BType_Mem Bit32 Bit8)))
          (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R7" (BType_Imm Bit32)))
             (BExp_Const (Imm32 4w))) BEnd_LittleEndian
          (BExp_Den (BVar "fr_270_R3" (BType_Imm Bit32)))``
*)
      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val (conds1, vars1, valm)  = bexp_to_smtlib conds  vars  expm;
          val (conds2, vars2, valad) = bexp_to_smtlib conds1 vars1 expad;
          val (conds3, vars3, valv)  = bexp_to_smtlib conds2 vars2 expv;

          val (_,stym) = valm;
          val (_,styad) = valad;
          val (_,styv) = valv;
          val () = endi_to_smtlib stym endi;

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_MEM (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val _ = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";
          val szadi = smt_type_bv_to_int styad_bvt;
          val szci  = smt_type_bv_to_int styc_bvt;

          val styv_bvt = case styv of
                    SMTTY_BV bvt => bvt
                  | _ => problem exp "can only write bitvectors to memory: ";
          val szi = smt_type_bv_to_int styv_bvt;

          (* current restrictions *)
          val _ = if szadi = 32 then () else
                    problem exp "address type other than 32bits cannot be handled currently: ";
          val _ = if szci  =  8 then () else
                    problem exp "cell types other than 8bits cannot be handled currently: ";
          val _ = if szi   =  8 orelse
                     szi   = 32 then () else
                    problem exp "load types other than 8 and 32bits cannot be handled currently: ";

          val z3funname = "storefun_" ^ (Int.toString szadi) ^
                                 "_" ^ (Int.toString szci) ^
                                 "_" ^ (Int.toString szi);
          val storeval = gen_smtlib_expr z3funname [valm, valad, valv] stym;
        in
          (conds3, vars3, storeval)
        end

      else
        problem exp "don't know BIR expression: "
    end;

(* poor man's unit test *)
local
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
val (conds, vars, str) = bexp_to_smtlib [] vars_empty exp;
(*
val vars = vars_empty;
val varlist = Redblackset.listItems vars;
*)

val result = querysmt smtlib_prelude vars [str];
in
end

end (* local *)

end (* struct *)
