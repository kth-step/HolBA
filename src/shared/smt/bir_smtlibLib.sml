structure bir_smtlibLib =
struct

local
  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expSyntax bir_immSyntax bir_envSyntax bir_exp_immSyntax bir_exp_memSyntax;
  open bir_bool_expSyntax;
  open bir_valuesSyntax;
  open wordsSyntax;

  open holba_z3Lib;

  val ERR = Feedback.mk_HOL_ERR "bir_smtlibLib";

  fun problem_gen fname t msg = 
    raise ERR fname (msg ^ (term_to_string t));

  val debug_print = false;

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
          (SMTTY_ARR (32, 8))
        else if is_BType_Mem btype andalso pair_eq identical identical (dest_BType_Mem btype) (Bit64_tm, Bit8_tm) then
          (SMTTY_ARR (64, 8))
        else problem_gen "bvar_to_smtlib_type" btype "don't know how to convert BIR type: "
    end;


  fun problem_gen_sty fname t sty =
    problem_gen fname t ("don't know how to convert as " ^ (smt_type_to_smtlib sty) ^ ": ");

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

  fun endi_to_smtlib endi (szci, szi) =
    if is_BEnd_LittleEndian endi then SMTMEM_LittleEndian
    else if is_BEnd_BigEndian endi then SMTMEM_BigEndian
    else if is_BEnd_NoEndian endi andalso szci = szi then SMTMEM_NoEndian
    else problem_gen "endi_to_smtlib" endi ("cannot convert endianness ("^ Int.toString szci ^", "^ Int.toString szi ^")");


val export_loadstore_asfunction = true;
val export_preprocessing = true;
val export_abbreviation_dict = true;
val export_abbreviation_load = true;
val export_abbreviation_store = true;
val export_abbreviation_from_query = true;

val (gen_smt_load, gen_smt_store) =
  if export_loadstore_asfunction then
    (gen_smt_load_as_funcall, gen_smt_store_as_funcall)
  else
    (gen_smt_load_as_exp, gen_smt_store_as_exp);

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

fun smtlib_wrap_to_bool   str = "(= #b1 " ^ str ^ ")";
fun smtlib_wrap_from_bool str = "(ite " ^ str ^ " #b1 #b0)";

fun to_smtlib_bool (str, sty) =
  if sty = SMTTY_Bool then
    (str, sty)
  else if sty = SMTTY_BV 1 then
    (smtlib_wrap_to_bool str, SMTTY_Bool)
  else
    raise ERR "to_smtlib_bool" ("cannot convert the given type to bool: " ^ (smt_type_to_smtlib sty));

  fun bexp_to_smtlib is_tl exst exp =
    let
      fun problem exp msg = problem_gen "bexp_to_smtlib" exp msg;
      
      (* solves syntactic sugar and constant word expressions in BExp_Const *)
      fun generic_solution err_msg exp_tm =
        let
          val eqexp = (snd o dest_eq o concl o EVAL) exp_tm;
        in
          if not (identical exp_tm eqexp) then
            bexp_to_smtlib is_tl exst eqexp
          else
            problem exp_tm err_msg
        end

      val abbr_o = exst_get_abbr exst exp;
    in
      if export_abbreviation_dict andalso isSome abbr_o then (exst, valOf abbr_o)
      else if export_abbreviation_from_query andalso is_tl andalso is_bir_eq_abbrevd exp then
        let
	  val (expval, expvar) = dest_bir_eq exp;
          val (exst1, v_var) = bexp_to_smtlib false exst expvar;
	  
	  val has_abbr = isSome (exst_get_abbr exst1 expval);
	  val exst2 = exst_set_abbr_skip exst1 true;
          val (exst3, v_val) = bexp_to_smtlib false exst2 expval;
	  val exst3 = exst_set_abbr_skip exst3 false;

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
        in
          if is_word_literal wv then
            let val vstr = (Arbnum.toString o dest_word_literal) wv in
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
          else
            generic_solution "can only handle word literals: " exp
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

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_ARR (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val () = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";

          val szadi = styad_bvt;
          val szci  = styc_bvt;
          val szi  = (size_of_bir_immtype_t) sz;
	  
          val smt_endi = endi_to_smtlib endi (szci, szi);

	  val loadval = gen_smt_load valm valad (smt_endi, szadi, szci, szi)
                        handle _ => problem exp "could not generate smt load expression";

	  val (exst3, v_var) =
	    if export_abbreviation_load then
	      abbreviate_exp exst2 abbr_skip "vv" (exp, loadval)
	    else
	      (exst2, loadval);
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

          val (styad_bvt, styc_bvt) = case stym of
                    SMTTY_ARR (ad, c) => (ad, c)
                  | _ => problem exp "memory must be of memory type: ";
          val _ = if styad = (SMTTY_BV styad_bvt) then () else
                    problem exp "address type doesn't match memory address type: ";
          val szadi = styad_bvt;
          val szci  = styc_bvt;

          val styv_bvt = case styv of
                    SMTTY_BV bvt => bvt
                  | _ => problem exp "can only write bitvectors to memory: ";
          val szi = styv_bvt;
	  
          val smt_endi = endi_to_smtlib endi (szci, szi);

          val storeval = gen_smt_store valm valad valv (smt_endi, szadi, szci, szi)
                         handle _ => problem exp "could not generate smt store expression";

	  val (exst4, m_var) =
	    if export_abbreviation_store then
	      abbreviate_exp exst3 abbr_skip "mv" (exp, storeval)
	    else
	      (exst3, storeval);
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
        generic_solution "don't know BIR expression: " exp
    end;

  (* preprocess into CNF, into list of conjuncted clauses *)
  (* TODO: all these rewritings are actually type-sensitive,
      would need to do typechecks (only practical when using a function that includes a dictionary for repeated typechecks for performance),
      and also would need to include is_BIExp_LessOrEqual for the implication rewriting *)
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
      exst_add_cond exst' (to_smtlib_bool e_smtlib)
    end;

  fun export_bexp e exst =
    (if not debug_print then () else
     (print "export_bexp:::\n"; print_term e);
     if not export_preprocessing then append_bexp e exst else
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
     end);

local
  (* TODO: need to add conversion from word to bir: values are constant bitvector/imm or constant array/memory *)
  (* TODO: also need variable name conversion, holv_ are going to be words, birv_ would be bir constant expressions *)
  fun modellines_to_pairs [] acc = acc
    | modellines_to_pairs [_] _ = raise ERR "modellines_to_pairs" "the returned model does not have an even number of lines"
    | modellines_to_pairs (vname::holterm::lines) acc =
        modellines_to_pairs lines ((vname, Parse.Term [QUOTE holterm])::acc);
  open wordsSyntax;
  open finite_mapSyntax;
in
  fun smtmodel_to_wordfmap model =
    rev (modellines_to_pairs model []);
  (*fun smtmodel_to_bexp model = ;*)
end

end (* local *)

end (* struct *)
