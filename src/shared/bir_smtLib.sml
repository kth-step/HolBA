structure bir_smtLib =
struct

local

  open holba_fileLib;
  open holba_exec_wrapLib;

  val ERR = Feedback.mk_HOL_ERR "bir_smtLib";

in

(* =========================================================== *)
(*
val z3bin = "/home/andreas/data/hol/HolBA_opt/z3-4.8.4/bin/z3";
*)
fun openz3 z3bin = 
  (Unix.execute (z3bin, ["-in"])) : (TextIO.instream, TextIO.outstream) Unix.proc;

fun endmeexit p = Unix.fromStatus (Unix.reap p);

fun get_streams p = Unix.streamsOf p;

val z3proc_bin_o = ref (NONE : string option);
val z3proc_o = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc) option);
val bir_smtLib_z3_prelude = read_from_file (holpathdb.subst_pathvars "$(HOLBADIR)/src/shared/bir_smtLib.z3_prelude");
val bir_smtLib_z3_prelude_n = bir_smtLib_z3_prelude ^ "\n";
val use_stack = true;
val debug_print = false;
fun get_z3proc z3bin =
  let
   val z3proc_ = !z3proc_o;
   fun check_and_restart z3p =
     if z3bin = valOf (!z3proc_bin_o) then z3p else
       let
         val _ = endmeexit z3p;
         val _ = z3proc_o := NONE;
       in
         get_z3proc z3bin
       end;
   val p = if isSome z3proc_ then check_and_restart (valOf z3proc_) else
      let
        val _ = if not debug_print then () else
	        print ("starting: " ^ z3bin ^ "\n");
        val p = openz3 z3bin;
	val _ = z3proc_bin_o := SOME z3bin;
	val _ = if not use_stack then () else
	 let
          val (_,s_out) = get_streams p;
          (* prepare prelude and push *)
          val () = TextIO.output (s_out, bir_smtLib_z3_prelude ^ "\n");
          val () = TextIO.output (s_out, "(push)\n");
	 in
	  ()
	 end;
      in (z3proc_o := SOME p; p) end;
  in
    p
  end;

fun sendreceive_query z3bin q =
 let
   val _ = if not debug_print then () else
           (print q; print "\n");
   val p = get_z3proc z3bin;
   val (s_in,s_out) = get_streams p;
   val _ = if not use_stack then
            TextIO.output (s_out, bir_smtLib_z3_prelude_n)
           else ();
   val () = TextIO.output (s_out, q);
   val out  = TextIO.input s_in;
   val _ = if not debug_print then () else
           (print out; print "\n\n");
   (* https://microsoft.github.io/z3guide/docs/logic/basiccommands/ *)
   val _ = if not use_stack then
            TextIO.output (s_out, "(reset)\n")
	   else
	    (TextIO.output (s_out, "(pop)\n");
	     TextIO.output (s_out, "(push)\n"));
 in
   out
 end;
(* =========================================================== *)

  datatype bir_smt_result =
      BirSmtSat
    | BirSmtUnsat
    | BirSmtUnknown;

  fun get_default_z3 () =
    case OS.Process.getEnv "HOL4_Z3_EXECUTABLE" of
      SOME z3bin => z3bin
    | NONE =>
      raise ERR "get_default_z3"
        "Z3 not configured: set the HOL4_Z3_EXECUTABLE environment variable to point to the Z3 executable file.";

  fun querysmt_raw z3bin_o timeout_o q =
      let
        val z3bin = case z3bin_o of
	     NONE => get_default_z3 ()
	   | SOME x => x;
	val (timeout_s_before, timeout_s_after) =
	  case timeout_o of
             NONE => ("", "")
           | SOME timeout => ("(set-option :timeout " ^ (Int.toString timeout) ^ ")\n\n", "(set-option :timeout 4294967295)\n");
	val q_wto =
	  (timeout_s_before ^
           q ^
	   timeout_s_after)
        val out = sendreceive_query z3bin q_wto;
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
      end

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
	  "(assert (> ("^"* a a) 3))\n" ^
	  "(assert (= (+ ("^"* b b b) ("^"* b c)) 3.0))\n" ^
	  "(check-sat)\n";

  val q = "(echo \"Z3 does not always find solutions to non-linear problems\")\n";

  val q = "(check-sat)\n";

  val result = querysmt_raw NONE NONE q;
  *)

  datatype bir_smt_type =
      SMTTY_Bool
    | SMTTY_BV   of int
    | SMTTY_MEM  of (int * int);

  fun smt_type_to_smtlib SMTTY_Bool          = "Bool"
    | smt_type_to_smtlib (SMTTY_BV  i)       = "(_ BitVec " ^ (Int.toString i) ^ ")"
    | smt_type_to_smtlib (SMTTY_MEM (ad, v)) = "(Array " ^ (smt_type_to_smtlib (SMTTY_BV ad)) ^
						     " " ^ (smt_type_to_smtlib (SMTTY_BV v)) ^ ")";

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

  (* TODO: this should be split into generic z3 interface and bir_z3 interface *)
  fun querysmt_gen z3bin_o timeout_o (vars, asserts) =
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
	querysmt_raw z3bin_o timeout_o
	       (decls       ^ "\n" ^
	        asserts_str ^ "\n" ^
	        "(check-sat)\n")
      end;

  val querysmt = querysmt_gen NONE;

  fun smtlib_exp_compare ((an, aty),(bn, bty)) =
    if an = bn then
      String.compare (smt_type_to_smtlib aty, smt_type_to_smtlib bty)
    else
      String.compare (an, bn);

  (*
  querysmt NONE (Redblackset.fromList smtlib_exp_compare [("x", SMTTY_BV 8)])
	   [("(= x #xFF)", SMTTY_Bool)]

  querysmt NONE (Redblackset.fromList smtlib_exp_compare [("x", SMTTY_BV 8)])
	   [("(= x #xFF)", SMTTY_Bool), ("(= x #xAA)", SMTTY_Bool)]
  *)

end (* local *)

(*
querysmt_raw NONE NONE "(simplify ((_ extract 3 2) #xFC))"

querysmt_raw NONE NONE "(simplify (bvor #x6 #x3))"

querysmt_raw NONE NONE "(display (_ bv20 16))"
*)

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expSyntax bir_immSyntax bir_envSyntax bir_exp_immSyntax bir_exp_memSyntax;
  open bir_bool_expSyntax;
  open bir_valuesSyntax;
  open wordsSyntax;

  open holba_fileLib;

  val ERR = Feedback.mk_HOL_ERR "bir_smtLib";

  fun problem_gen fname t msg = 
    raise ERR fname (msg ^ (term_to_string t));

in

  fun hvar_to_smtlib_ref hv =
    "holv_" ^ ((fst o dest_var) hv);

  fun hvar_to_smtlib_type hv =
    if not ((wordsSyntax.is_word_type o type_of) hv) then
      problem_gen "hvar_to_smtlib_type" hv "don't know how to convert HOL type, must be word type: "
    else
    let
      val hwsize = (Arbnum.toInt o wordsSyntax.size_of) hv;
    in
        if hwsize = 1 then
          SMTTY_Bool
        else if hwsize = 8 then
          (SMTTY_BV  8)
        else if hwsize = 16 then
          (SMTTY_BV 16)
        else if hwsize = 32 then
          (SMTTY_BV 32)
        else if hwsize = 64 then
          (SMTTY_BV 64)
        else
	  problem_gen "hvar_to_smtlib_type" hv "don't know how to convert HOL type, bad word size: "
    end;

  fun bvar_to_smtlib_ref bv =
    "birv_" ^ ((fst o dest_BVar_string) bv);

  fun bvar_to_smtlib_type bv =
    let
      val btype = (snd o dest_BVar_string) bv;
    in
        if      is_BType_Imm1  btype orelse is_BType_Bool btype then
          SMTTY_Bool
        else if is_BType_Imm8  btype then
          (SMTTY_BV  8)
        else if is_BType_Imm16 btype then
          (SMTTY_BV 16)
        else if is_BType_Imm32 btype then
          (SMTTY_BV 32)
        else if is_BType_Imm64 btype then
          (SMTTY_BV 64)
        else if is_BType_Mem btype andalso pair_eq identical identical (dest_BType_Mem btype) (Bit32_tm, Bit8_tm) then
          (SMTTY_MEM (32, 8))
        else if is_BType_Mem btype andalso pair_eq identical identical (dest_BType_Mem btype) (Bit64_tm, Bit8_tm) then
          (SMTTY_MEM (64, 8))
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
(* highcast: highest bits for downcasting, otherwise like lowcast *)
(* signedcast: preserve signed bit for upcasting, otherwise like unsignedcast *)
  fun castt_to_smtlib castt str szi_from szi_to =
    if szi_from >= szi_to then
      if is_BIExp_LowCast castt orelse
         is_BIExp_UnsignedCast castt orelse
         is_BIExp_SignedCast castt then
        "((_ extract " ^ (Int.toString (szi_to-1)) ^ " 0) " ^ str ^ ")"
      else if is_BIExp_HighCast castt then
        "((_ extract " ^ (Int.toString (szi_from - 1)) ^
                   " " ^ (Int.toString (szi_from - szi_to)) ^
                  ") " ^ str ^ ")"
      else raise ERR "castt_to_smtlib" "don't know casttype"
    else
      if is_BIExp_LowCast castt orelse
         is_BIExp_UnsignedCast castt orelse
         is_BIExp_HighCast castt then
        "(concat #b" ^ (mk_0s (szi_to - szi_from)) ^ " " ^ str ^ ")"
      else if is_BIExp_SignedCast castt then
        "((_ sign_extend " ^ (Int.toString (szi_to - szi_from)) ^ ") " ^ str ^ ")"
      else raise ERR "castt_to_smtlib" "don't know casttype";

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
    (* simple equality *)
    (* TODO: BinPred cannot be applied to memories! *)
    if is_BIExp_Equal bpredop then gen_exp "="
    else if is_BIExp_NotEqual bpredop then apply_smtlib_op (fn s => "(not " ^ s ^ ")")
                                                           (gen_exp "=")
    (* bitvectors *)
    else if smt_type_is_bv sty then
      if is_BIExp_LessThan bpredop then gen_exp "bvult"
      else if is_BIExp_SignedLessThan bpredop then gen_exp "bvslt"
      else if is_BIExp_LessOrEqual bpredop then gen_exp "bvule"
      else if is_BIExp_SignedLessOrEqual bpredop then gen_exp "bvsle"
      else problem_gen_sty "bpredop_to_smtlib" bpredop sty
    (* bools *)
    (* TODO: BinPred can be applied to Imm1, handle remaining cases here! *)
    else if smt_type_is_bool sty then
      if is_BIExp_LessOrEqual bpredop then gen_exp "=>"
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


fun gen_smt_load_v1 valm valad (szadi, szci, szi) =
  let
          (* current restrictions *)
          val () = if szadi = 32 orelse szadi = 64 then () else
                    raise ERR "gen_smt_load_v1" "address type other than 32 or 64bits cannot be handled currently: ";
          val () = if szci  =  8 then () else
                    raise ERR "gen_smt_load_v1" "cell types other than 8bits cannot be handled currently: ";
          val () = if szi   =  8 orelse
                     szi   = 16 orelse
                     szi   = 32 orelse
                     szi   = 64 then () else
                    raise ERR "gen_smt_load_v1" "load types other than 8, 16, 32 and 64bits cannot be handled currently: ";

          val z3funname = "loadfun_" ^ (Int.toString szadi) ^
                                 "_" ^ (Int.toString szci) ^
                                 "_" ^ (Int.toString szi);

          val loadval = gen_smtlib_expr z3funname [valm, valad] (SMTTY_BV szi);
  in
    loadval
  end;


fun gen_smt_store_v1 valm valad valv (szadi, szci, szi) =
  let
          (* current restrictions *)
          val _ = if szadi = 32 orelse szadi = 64 then () else
                    raise ERR "gen_smt_store_v1" "address type other than 32 or 64bits cannot be handled currently: ";
          val _ = if szci  =  8 then () else
                    raise ERR "gen_smt_store_v1" "cell types other than 8bits cannot be handled currently: ";
          val _ = if szi   =  8 orelse
                     szi   = 16 orelse
                     szi   = 32 orelse
                     szi   = 64 then () else
                    raise ERR "gen_smt_store_v1" "store types other than 8, 16, 32 and 64bits cannot be handled currently: ";

          val z3funname = "storefun_" ^ (Int.toString szadi) ^
                                 "_" ^ (Int.toString szci) ^
                                 "_" ^ (Int.toString szi);

          val storeval = gen_smtlib_expr z3funname [valm, valad, valv] (snd valm);
  in
    storeval
  end;

(*
fun problem_exp s = raise ERR "some problem" s;
val (szadi, szci, szi) = (64,8,32);
val valm = ("mem1", SMTTY_MEM (szadi, szci));
val valad = ("mem_ad1", SMTTY_BV szadi);
val valv = ("mem_v1", SMTTY_BV szi);
*)
fun gen_smt_load_v2 valm valad (szadi, szci, szi) =
  let
          fun gen_addr_const i = "(_ bv" ^ (Int.toString i) ^ " " ^ (Int.toString szadi) ^ ")";
          fun gen_addr_val i = ("(bvadd " ^ (fst valad) ^ " " ^ (gen_addr_const i) ^ ")", SMTTY_BV szadi);
	  
          val selects = List.tabulate (szi div 8, fn i => gen_smtlib_expr "select" [valm, gen_addr_val i] (SMTTY_BV szci));
	  (* TODO: other endianness can be easily implemented here *)
	  val loadval = gen_smtlib_expr "concat" (rev selects) (SMTTY_BV szi);
  in
    loadval
  end;

fun gen_smt_store_v2 valm valad valv (szadi, szci, szi) =
  let
          fun gen_addr_const i = "(_ bv" ^ (Int.toString i) ^ " " ^ (Int.toString szadi) ^ ")";
          fun gen_addr_val i = ("(bvadd " ^ (fst valad) ^ " " ^ (gen_addr_const i) ^ ")", SMTTY_BV szadi);

          fun gen_extract_val i = ("((_ extract "^(Int.toString ((i+1)*szci-1))^" "^(Int.toString (i*szci))^") " ^ (fst valv) ^ ")", SMTTY_BV szci);

          fun gen_store a i = gen_smtlib_expr "store" [a, gen_addr_val i, gen_extract_val i] (snd valm);
	  val idxs = List.tabulate (szi div 8, I);
	  
	  (* TODO: other endianness can be easily implemented here *)
          val storeval = List.foldl (fn (i,a) => gen_store a i) valm (rev idxs);
  in
    storeval
  end;

val gen_smt_load = gen_smt_load_v1;
val gen_smt_store = gen_smt_store_v1;

val exst_empty =
 ((Redblackset.empty smtlib_exp_compare) : (string * bir_smt_type) Redblackset.set,
  (Redblackset.empty smtlib_exp_compare) : (string * bir_smt_type) Redblackset.set,
  0:int,
  (Redblackmap.mkDict Term.compare) : (term, string * bir_smt_type) Redblackmap.dict,
  false);

fun exst_add_var (conds, vars, abbr_idx, abbr_dict, abbr_skip) v =
  (conds, Redblackset.add(vars, v), abbr_idx, abbr_dict, abbr_skip);

fun exst_add_cond (conds, vars, abbr_idx, abbr_dict, abbr_skip) cond =
  (Redblackset.add(conds, cond), vars, abbr_idx, abbr_dict, abbr_skip);

fun exst_get_abbr_idx (conds, vars, abbr_idx, abbr_dict, abbr_skip) =
  ((conds, vars, abbr_idx + 1, abbr_dict, abbr_skip), abbr_idx);

fun exst_add_abbr (conds, vars, abbr_idx, abbr_dict, abbr_skip) t t_var =
  if not (isSome (Redblackmap.peek (abbr_dict, t))) then
    (conds, vars, abbr_idx, Redblackmap.insert (abbr_dict, t, t_var), abbr_skip)
  else
    raise ERR "exst_add_abbr" "this should not happen, something is wrong, should not need to map the same term to two different abbreviations";

fun exst_get_abbr (conds, vars, abbr_idx, abbr_dict, abbr_skip) t =
  Redblackmap.peek (abbr_dict, t);

fun exst_get_abbr_skip (conds, vars, abbr_idx, abbr_dict, abbr_skip) =
  ((conds, vars, abbr_idx, abbr_dict, false), abbr_skip);

fun exst_set_abbr_skip (conds, vars, abbr_idx, abbr_dict, abbr_skip) v =
  (conds, vars, abbr_idx, abbr_dict, v);

fun exst_to_querysmt (conds, vars, abbr_idx, abbr_dict, abbr_skip) =
  let
    val condsl = Redblackset.listItems conds;
  in
    (vars, condsl)
  end

fun abbreviate_exp exst abbr_skip v_varprefix (t, v_val) =
  if abbr_skip then (exst, v_val) else
  let
    val (exst1, abbr_idx) = exst_get_abbr_idx exst;
    val v_varname = v_varprefix ^ "_" ^ (Int.toString abbr_idx);
    val v_var = (v_varname, snd v_val);
    val v_var_cond = gen_smtlib_expr "=" [v_val, v_var] SMTTY_Bool;

    val exst2 = exst_add_cond (exst_add_var exst1 v_var) v_var_cond;
    val exst3 = exst_add_abbr exst2 t v_var;
  in
    (exst3, v_var)
  end;

 local
   fun is_bir_binop is_bop_fun e =
     if not (is_BExp_BinExp e) then false else
     let
       val (bop,_,_) = dest_BExp_BinExp e;
     in
       is_bop_fun bop
     end;
   fun is_bir_unop is_uop_fun e =
     if not (is_BExp_UnaryExp e) then false else
     let
       val (uop,_) = dest_BExp_UnaryExp e;
     in
       is_uop_fun uop
     end;
   fun is_bir_bpop is_bpop_fun e =
     if not (is_BExp_BinPred e) then false else
     let
       val (bpop,_,_) = dest_BExp_BinPred e;
     in
       is_bpop_fun bpop
     end;
 in
   val is_bir_den = is_BExp_Den;
   fun is_bir_constfv e =
     (is_BExp_Const e) andalso
     ((is_var o snd o gen_dest_Imm o dest_BExp_Const) e);
   val is_bir_and = is_bir_binop is_BIExp_And;
   val is_bir_or = is_bir_binop is_BIExp_Or;
   val is_bir_neg = is_bir_unop is_BIExp_Not;
   val is_bir_eq = is_bir_bpop is_BIExp_Equal;
   fun mk_bir_neg e = mk_BExp_UnaryExp (BIExp_Not_tm, e);
   fun mk_bir_eq (e1,e2) = mk_BExp_BinPred (BIExp_Equal_tm, e1, e2);

   (* the following group of functions are only correct if the corresponding is_... functions have been applied before and return true *)
   val dest_bir_or = (fn (_,e1,e2) => (e1,e2)) o dest_BExp_BinExp;
   val dest_bir_and = dest_bir_or;
   val dest_bir_neg = snd o dest_BExp_UnaryExp;
   val dest_bir_eq = (fn (_,e1,e2) => (e1,e2)) o dest_BExp_BinPred;
   val get_bir_eq_den_left =
     fst o dest_bir_eq;

   fun is_bir_neg_or e = (is_bir_neg e) andalso ((is_bir_or o dest_bir_neg) e);
   val dest_bir_neg_or = dest_bir_or o dest_bir_neg;
   fun is_bir_neg_neg e = (is_bir_neg e) andalso ((is_bir_neg o dest_bir_neg) e);
   val dest_bir_neg_neg = dest_bir_neg o dest_bir_neg;
   fun is_bir_eq_denfv e = (is_bir_eq e) andalso (((fn t => (is_bir_den t) orelse (is_bir_constfv t)) o snd o dest_bir_eq) e);
 end;

(* this has to match exactly the condition under which abbreviations are applied in bexp_to_smtlib *)
fun is_bir_eq_abbrevd e =
  ((is_bir_eq_denfv) e) andalso
  (((fn t => is_BExp_Load t orelse is_BExp_Store t) o get_bir_eq_den_left) e);

  fun bexp_to_smtlib is_tl exst exp =
    let
      fun problem exp msg = problem_gen "bexp_to_smtlib" exp msg;

      fun smtlib_wrap_to_bool   str = "(= #b1 " ^ str ^ ")";
      fun smtlib_wrap_from_bool str = "(ite " ^ str ^ " #b1 #b0)";

      val abbr_o = exst_get_abbr exst exp;
    in
      if isSome abbr_o then (exst, valOf abbr_o)
      else if is_tl andalso is_bir_eq_abbrevd exp then
        let
	  val (expval, expvar) = dest_bir_eq exp;
          val (exst1, v_var) = bexp_to_smtlib false exst expvar;
	  
	  val has_abbr = isSome (exst_get_abbr exst1 expval);
	  val exst2 = exst_set_abbr_skip exst1 true;
          val (exst3, v_val) = bexp_to_smtlib false exst2 expval;

          val args = [v_val, v_var];
          fun probfun () = problem exp "equality needs same type for both sides: ";
          val _ = get_smtlib_type_args probfun args;
          val v_var_cond = gen_smtlib_expr "=" args SMTTY_Bool;

          (* this must be done with care, can only be at toplevel and the resulting assertion have to be added to the conds in the exporter state *)
	  (* maybe should just add it to the state, as it is a set it will not be added twice anyways? *)
          val exst4 = if has_abbr then exst3 else exst_add_abbr exst3 expval v_var;
	in
	  (exst4, v_var_cond)
	end
      else if is_BExp_Const exp then
        if (is_var o snd o gen_dest_Imm o dest_BExp_Const) exp then
          let
            val hv    = (snd o gen_dest_Imm o dest_BExp_Const) exp;
            val sname = hvar_to_smtlib_ref  hv;
            val stype = hvar_to_smtlib_type hv;
            val var   = (sname, stype);
          in
            (exst_add_var exst var, var)
          end
	else
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
              (exst, ("true", SMTTY_Bool))
            else
              (exst, ("false", SMTTY_Bool))
          else
            (exst, ("(_ bv" ^ vstr ^ " " ^ (Int.toString sz) ^ ")",
               SMTTY_BV sz))
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
          (exst_add_var exst var, var)
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
          val (exst1, (stre, stye)) = bexp_to_smtlib false exst exp;

          val szi = size_of_bir_immtype_t sz;
          val sty = SMTTY_BV szi;
          val exp_szi = case stye of
                           SMTTY_BV i => i
                         | _ => problem exp "cast can only be applied to imm (not imm1): ";

          val caststr = castt_to_smtlib castt stre exp_szi szi;

          val castval = (caststr, sty);
        in
          (exst1, castval)
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp_) = (dest_BExp_UnaryExp) exp;

          val (exst1, (str, sty)) = bexp_to_smtlib false exst exp_;
          val (str, sty) = if not (is_BIExp_Not uop) then (str, sty) else
                         case sty of
                           SMTTY_BV 1 => ("(= " ^ str ^ " (_ bv1 1))", SMTTY_Bool)
                         | SMTTY_BV _ => problem exp "unsupported argument type: " ()
                         | _ => (str, sty);

          val uopval = uop_to_smtlib uop (str, sty);
        in
          (exst1, uopval)
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val (exst1, val1) = bexp_to_smtlib false exst  exp1;
          val (exst2, val2) = bexp_to_smtlib false exst1 exp2;
          val args = [val1, val2];

          val sty =
            get_smtlib_type_args
              (fn () => problem exp "binary operator needs same type for both sides: ")
              args;
          val bopstr = bop_to_smtlib sty bop;
                                         
          val bopval = gen_smtlib_expr bopstr args sty;
        in
          (exst2, bopval)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val (exst1, val1) = bexp_to_smtlib false exst  exp1;
          val (exst2, val2) = bexp_to_smtlib false exst1 exp2;
          val args = [val1, val2];

          fun probfun () = problem exp "binary predicate operator needs same type for both sides: ";

          val bpredopval = bpredop_to_smtlib probfun bpredop args;
        in
          (exst2, bpredopval)
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
          val (exst1, (strc, styc)) = bexp_to_smtlib false exst  expc;
          val (exst2, (strt, styt)) = bexp_to_smtlib false exst1 expt;
          val (exst3, (strf, styf)) = bexp_to_smtlib false exst2 expf;
          val _ = if smt_type_is_bool styc then () else
                  problem exp "if-then-else needs bool in condition: ";
          val _ = if styt = styf then () else
                  problem exp "if-then-else needs same type for both sides: ";
        in
          (exst3, ("(ite " ^ strc ^ " " ^ strt ^ " " ^ strf ^ ")", styt))
        end

(*
fun problem _ _ = raise ERR "" "";
val exst = exst_empty;
val exp = ``
BExp_Load (BExp_Den (BVar "fr_269_MEM" (BType_Mem Bit32 Bit8)))
          (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R7" (BType_Imm Bit32)))
             (BExp_Const (Imm32 4w))) BEnd_LittleEndian Bit32``
*)
      else if is_BExp_Load exp then
        let
	  val (exst, abbr_skip) = exst_get_abbr_skip exst;
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val (exst1, valm)  = bexp_to_smtlib false exst  expm;
          val (exst2, valad) = bexp_to_smtlib false exst1 expad;

          val (_,stym) = valm;
          val (_,styad) = valad;
          val _ = endi_to_smtlib stym endi;

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_MEM (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val () = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";

          val szadi = styad_bvt;
          val szci  = styc_bvt;
          val szi  = (size_of_bir_immtype_t) sz;

	  val loadval = gen_smt_load valm valad (szadi, szci, szi)
                        handle _ => problem exp "could not generate smt load expression";

	  val (exst3, v_var) = abbreviate_exp exst2 abbr_skip "vv" (exp, loadval);
        in
	  (exst3, v_var)
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
	  val (exst, abbr_skip) = exst_get_abbr_skip exst;
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val (exst1, valm)  = bexp_to_smtlib false exst  expm;
          val (exst2, valad) = bexp_to_smtlib false exst1 expad;
          val (exst3, valv)  = bexp_to_smtlib false exst2 expv;

          val (_,stym) = valm;
          val (_,styad) = valad;
          val (_,styv) = valv;
          val () = endi_to_smtlib stym endi;

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_MEM (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val _ = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";
          val szadi = styad_bvt;
          val szci  = styc_bvt;

          val styv_bvt = case styv of
                    SMTTY_BV bvt => bvt
                  | _ => problem exp "can only write bitvectors to memory: ";
          val szi = styv_bvt;

          val storeval = gen_smt_store valm valad valv (szadi, szci, szi)
                         handle _ => problem exp "could not generate smt store expression";

	  val (exst4, m_var) = abbreviate_exp exst3 abbr_skip "mv" (exp, storeval);
        in
          (exst4, m_var)
        end

      else if bir_bool_expSyntax.is_bir_exp_false exp then
        (exst, ("false", SMTTY_Bool))
      else if bir_bool_expSyntax.is_bir_exp_true  exp then
        (exst, ("true",  SMTTY_Bool))

      else
        (* TODO: this is a generic solution for BIR syntactic sugar but we actually
                 want to export some specific expressions in a direct way, if possible *)
        let
          val eqexp = (snd o dest_eq o concl o EVAL) exp;
        in
          if not (identical exp eqexp) then
            bexp_to_smtlib is_tl exst eqexp
          else
            problem exp "don't know BIR expression: "
        end
    end;

  (* preprocess into CNF, into list of conjuncted clauses *)
  fun preprocess_bexp acc [] = acc
    | preprocess_bexp acc (e::l) =
    if is_bir_and e then
      let
        val (e1, e2) = dest_bir_and e;
      in
        preprocess_bexp acc (e1::e2::l)
      end
    else if is_bir_neg_or e then
      let
        val (e1, e2) = dest_bir_neg_or e;
	val e1' = mk_bir_neg e1;
	val e2' = mk_bir_neg e2;
      in
        preprocess_bexp acc (e1'::e2'::l)
      end
    else if is_bir_neg_neg e then
      let
        val e1 = dest_bir_neg_neg e;
      in
        preprocess_bexp acc (e1::l)
      end
    else if is_bir_eq e then
      let
        val (e1, e2) = dest_bir_eq e;
      in
        if is_bir_den e2 then
	  preprocess_bexp (e::acc) l
	else if not (is_bir_den e1) then
	  preprocess_bexp (e::acc) l
	else
	  preprocess_bexp ((mk_bir_eq (e2, e1))::acc) l
      end
    else
      preprocess_bexp (e::acc) l;

  fun append_bexp e exst =
    let
      val (exst', e_smtlib) = bexp_to_smtlib true exst e;
    in
      exst_add_cond exst' e_smtlib
    end;

  fun export_bexp e exst =
    let
      val es = preprocess_bexp [] [e];
      (*val es = [e]*)
      val (exst, _) = foldl
        (fn (e,(exst,acc)) =>
          if Redblackset.member(acc,e) then (exst,acc) else
	  (append_bexp e exst, Redblackset.add(acc,e)))
	(exst, Redblackset.empty Term.compare)
	es;
    in
      exst
    end;

(* TODO: add a model importer *)

end (* local *)

end (* struct *)
