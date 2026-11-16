open HolKernel Parse boolLib bossLib;

open bir_expSyntax bir_immSyntax bir_exp_immSyntax bir_valuesSyntax;

open holba_z3Lib;
open bir_smtlibLib;

val _ = new_theory "scratch";

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

(* Checks the SMT-LIB translation of BExp_Cast, and of the other operations
   on one-bit values, against the BIR semantics.
   One-bit values, such as comparisons, are SMT Bools in the translation,
   and BIR zero-extends them for every cast kind. *)

val cast_kinds = TypeBase.constructors_of bir_cast_t_ty;
val imm_types = bir_immtype_t_list;

fun canonical_imm v =
  let
    val (n, w) = gen_dest_Imm v;
    val k = wordsSyntax.dest_word_literal w;
  in
    mk_Imm_of_num n (Arbnum.mod (k, Arbnum.pow (Arbnum.two, Arbnum.fromInt n)))
  end;

fun imm_value v =
  let
    val (n, w) = gen_dest_Imm v;
  in
    (n, wordsSyntax.dest_word_literal w)
  end;

fun bir_eval_closed_imm e =
  (canonical_imm o dest_BVal_Imm o optionSyntax.dest_some o rhs o concl o EVAL)
    ``bir_eval_exp ^e bir_env_empty``
  handle HOL_ERR _ =>
    raise Fail ("bir_eval_exp does not give an immediate literal for: " ^ term_to_string e);

fun smt_unsat e = bir_smtLib.bir_smt_check_unsat false e;
fun smt_sat e = bir_smtLib.bir_smt_check_sat false e;

fun smt_type_of e = (snd o snd) (bexp_to_smtlib false exst_empty e);

fun check_against_eval e =
  let
    val v = bir_eval_closed_imm e;
    val e_eq_v = mk_BExp_BinPred (BIExp_Equal_tm, e, mk_BExp_Const v);
    val e_neq_v = mk_BExp_UnaryExp (BIExp_Not_tm, e_eq_v);
  in
    if smt_unsat e_neq_v andalso smt_sat e_eq_v then () else
      raise Fail ("translation disagrees with bir_eval_exp, which gives " ^
                  term_to_string v ^ ", for: " ^ term_to_string e)
  end;

fun check_casts_against_eval args =
  List.app (fn a =>
    List.app (fn ct =>
      List.app (fn ty =>
        check_against_eval (mk_BExp_Cast (ct, a, ty)))
      imm_types)
    cast_kinds)
  args;

fun covers_both_values es =
  let
    val vs = List.map (snd o imm_value o bir_eval_closed_imm) es;
  in
    List.exists (fn v => v = Arbnum.zero) vs andalso List.exists (fn v => v = Arbnum.one) vs
  end;


val _ = print "Casts of one-bit constants, comparisons and casts to Bit1\n";

val bool_consts = [
  ``BExp_Const (Imm1 0w)``,
  ``BExp_Const (Imm1 1w)``
];

val bool_cmps = [
  ``BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w)) (BExp_Const (Imm64 1w))``,
  ``BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 7w)) (BExp_Const (Imm64 1w))``,
  ``BExp_BinPred BIExp_SignedLessThan (BExp_Const (Imm32 0xFFFFFFFFw)) (BExp_Const (Imm32 0w))``,
  ``BExp_BinPred BIExp_Equal (BExp_Const (Imm8 3w)) (BExp_Const (Imm8 4w))``
];

val bool_casts = [
  ``BExp_Cast BIExp_LowCast (BExp_Const (Imm64 3w)) Bit1``,
  ``BExp_Cast BIExp_HighCast (BExp_Const (Imm16 0x7FFFw)) Bit1``
];

val _ = if List.all covers_both_values [bool_consts, bool_cmps, bool_casts] then () else
        raise Fail "each group of one-bit arguments must contain both values";

val _ = if List.all (fn a => smt_type_of a = SMTTY_Bool) (bool_consts @ bool_cmps @ bool_casts) then () else
        raise Fail "one-bit arguments must translate to SMT Bools";

val _ = check_casts_against_eval (bool_consts @ bool_cmps @ bool_casts);


val _ = print "seqz and snez with a free 64-bit variable\n";

val x = ``BExp_Den (BVar "x" (BType_Imm Bit64))``;
val x_is_0 = ``BExp_BinPred BIExp_Equal ^x (BExp_Const (Imm64 0w))``;

fun seqz ct = ``BExp_Cast ^ct (BExp_BinPred BIExp_LessThan ^x (BExp_Const (Imm64 1w))) Bit64``;
fun snez ct = ``BExp_Cast ^ct (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w)) ^x) Bit64``;
val seqz_ite = ``BExp_IfThenElse ^x_is_0 (BExp_Const (Imm64 1w)) (BExp_Const (Imm64 0w))``;
val snez_ite = ``BExp_IfThenElse ^x_is_0 (BExp_Const (Imm64 0w)) (BExp_Const (Imm64 1w))``;

(* the equivalence holds in BIR for every value of x ... *)
val env_w = ``BEnv (("x" =+ SOME (BVal_Imm (Imm64 w))) bir_env_map_empty)``;
val lo_thms = [blastLib.BBLAST_PROVE ``!w:word64. w <+ 1w <=> (w = 0w)``,
               blastLib.BBLAST_PROVE ``!w:word64. 0w <+ w <=> (w <> 0w)``];
fun bir_equiv_goal (e1, e2) = ``!w. bir_eval_exp ^e1 ^env_w = bir_eval_exp ^e2 ^env_w``;
val bir_equiv_tac =
  GEN_TAC >>
  CONV_TAC EVAL >>
  Cases_on `w = 0w` >>
  ASM_SIMP_TAC (srw_ss()) (bitTheory.DIV_2EXP_def :: lo_thms);
fun prove_bir_equiv eqn = prove (bir_equiv_goal eqn, bir_equiv_tac);

fun mk_neq (e1, e2) = mk_BExp_UnaryExp (BIExp_Not_tm, mk_BExp_BinPred (BIExp_Equal_tm, e1, e2));

(* ... and z3 must find it valid for the translation *)
fun check_equiv (e1, e2) =
  let
    val _ = prove_bir_equiv (e1, e2);
  in
    if smt_unsat (mk_neq (e1, e2)) then () else
      raise Fail ("translation of the following is not valid: " ^ term_to_string e1 ^
                  " = " ^ term_to_string e2)
  end;

(* both checks must reject an equivalence that does not hold *)
fun check_not_equiv (e1, e2) =
  let
    val proved = (TAC_PROOF (([], bir_equiv_goal (e1, e2)), bir_equiv_tac); true)
                 handle HOL_ERR _ => false;
  in
    if not proved andalso smt_sat (mk_neq (e1, e2)) then () else
      raise Fail ("the following is accepted although it does not hold: " ^ term_to_string e1 ^
                  " = " ^ term_to_string e2)
  end;

val _ = List.app (fn ct => (check_equiv (seqz ct, seqz_ite);
                            check_equiv (snez ct, snez_ite);
                            check_not_equiv (seqz ct, snez_ite)))
        cast_kinds;


val _ = print "Signed cast of a one-bit value is a zero extension\n";

val scast_1 = ``BExp_Cast BIExp_SignedCast (BExp_Const (Imm1 1w)) Bit64``;
val all_ones = ``BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw)``;

val _ = if imm_value (bir_eval_closed_imm scast_1) = (64, Arbnum.one) then () else
        raise Fail "bir_eval_exp does not give 1 for the signed cast of Imm1 1w to Bit64";
val _ = check_against_eval scast_1;
val _ = if smt_unsat (mk_BExp_BinPred (BIExp_Equal_tm, scast_1, all_ones)) then () else
        raise Fail "signed cast of Imm1 1w to Bit64 is translated as a sign extension";
val _ = if smt_unsat (mk_BExp_BinPred (BIExp_Equal_tm, seqz BIExp_SignedCast_tm, all_ones)) then () else
        raise Fail "signed cast of a comparison to Bit64 is translated as a sign extension";


val _ = print "Casts of bit-vector constants\n";

(* 1, only the sign bit, the sign bit and bit 0, all ones *)
fun bv_values n =
  let
    val sign = Arbnum.pow (Arbnum.two, Arbnum.fromInt (n - 1));
    val all_ones = Arbnum.less1 (Arbnum.pow (Arbnum.two, Arbnum.fromInt n));
  in
    [Arbnum.one, sign, Arbnum.plus1 sign, all_ones]
  end;

val bv_args =
  List.concat (List.map (fn ty =>
    let
      val n = size_of_bir_immtype_t ty;
    in
      List.map (fn v => mk_BExp_Const (mk_Imm_of_num n v)) (bv_values n)
    end)
  (List.filter (fn ty => size_of_bir_immtype_t ty > 1) imm_types));

val _ = check_casts_against_eval bv_args;


val _ = print "Other operations the translation supports on one-bit values\n";

val bits = [``BExp_Const (Imm1 0w)``, ``BExp_Const (Imm1 1w)``];
val bit_pairs = List.concat (List.map (fn a => List.map (fn b => (a, b)) bits) bits);

val one_bit_exps =
  List.concat (List.map (fn (a, b) =>
    List.map (fn bop => mk_BExp_BinExp (bop, a, b)) [BIExp_And_tm, BIExp_Or_tm, BIExp_Xor_tm] @
    List.map (fn bp => mk_BExp_BinPred (bp, a, b)) [BIExp_Equal_tm, BIExp_NotEqual_tm, BIExp_LessOrEqual_tm] @
    List.map (fn c => mk_BExp_IfThenElse (c, a, b)) bits)
  bit_pairs) @
  List.concat (List.map (fn a =>
    List.map (fn uop => mk_BExp_UnaryExp (uop, a)) [BIExp_Not_tm, BIExp_ChangeSign_tm])
  bits);

val _ = List.app check_against_eval one_bit_exps;

val _ = print "All tests passed\n";
