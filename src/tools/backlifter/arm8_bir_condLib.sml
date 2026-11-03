structure arm8_bir_condLib :> arm8_bir_condLib =
struct

open HolKernel boolLib Parse bossLib;

open wordsTheory;
open bir_bool_expTheory bir_expTheory;
open bir_exp_liftingTheory bir_lifting_machinesTheory;
open bir_exp_liftingLib;
open arm8_bir_condTheory;

val ERR = mk_HOL_ERR "arm8_bir_condLib";

val is_bir_is_bool_exp = can (match_term ``bir_is_bool_exp e``);

type arm8_bir_cond_result =
  { bir_def    : thm,
    lifted_thm : thm,
    pc_addr    : term option }

(* ------------------ *)
(* Supported fragment *)
(* ------------------ *)

val word64_ty = wordsSyntax.mk_int_word_type 64;
val arm8_state_ty = ``:arm8_state``;
val REG_tm = ``arm8_state_REG``;
val PC_tm = ``arm8_state_PC``;

fun unsupported what tm =
  raise ERR "arm8_cond_to_bir"
    ("unsupported " ^ what ^ ": " ^ term_to_string tm);

(* The word sizes of BIR immediates, except Bit1 and Bit128 *)
fun is_supported_word_ty ty =
  mem (fcpSyntax.dest_int_numeric_type (wordsSyntax.dest_word_type ty))
    [8, 16, 32, 64]
  handle HOL_ERR _ => false;

(* Word operations, applied to supported words *)
val word_unops = [``word_2comp``, ``word_1comp``, ``w2w``, ``sw2sw``];
val word_binops = [
  ``word_add``, ``word_sub``, ``word_mul``,
  ``word_div``, ``word_quot``, ``word_mod``,
  ``word_and``, ``word_or``, ``word_xor``];

(* Words built with the operations above from m.REG k with k a literal,
   free variables among the parameters, and literals *)
fun check_word params m tm =
  if not (is_supported_word_ty (type_of tm)) then unsupported "word type" tm
  else if wordsSyntax.is_word_literal tm then ()
  else if is_var tm then
    (if tmem tm params then () else unsupported "free variable" tm)
  else let
    val (f, args) = strip_comb tm
    fun is_op ops = is_const f andalso exists (same_const f) ops
  in
    case args of
      [a] =>
        if is_op word_unops then check_word params m a
        else unsupported "word term" tm
    | [a, b] =>
        if same_const f REG_tm andalso aconv m a then
          (if wordsSyntax.is_word_literal b then ()
           else unsupported "register index" b)
        else if is_op word_binops then
          (check_word params m a; check_word params m b)
        else unsupported "word term" tm
    | _ => unsupported "word term" tm
  end;

val word_preds = [
  wordsSyntax.dest_word_lo, wordsSyntax.dest_word_ls,
  wordsSyntax.dest_word_hi, wordsSyntax.dest_word_hs,
  wordsSyntax.dest_word_lt, wordsSyntax.dest_word_le,
  wordsSyntax.dest_word_gt, wordsSyntax.dest_word_ge];

fun check_bool params m tm =
  if is_conj tm orelse is_disj tm orelse is_imp_only tm then
    let val (a, b) = dest_comb tm |> (fn (l, r) => (rand l, r))
    in (check_bool params m a; check_bool params m b) end
  else if is_neg tm then check_bool params m (dest_neg tm)
  else if is_eq tm then let
    val (a, b) = dest_eq tm
  in (check_word params m a; check_word params m b) end
  else case List.mapPartial (fn d => SOME (d tm) handle HOL_ERR _ => NONE) word_preds of
    [(a, b)] => (check_word params m a; check_word params m b)
  | _ => unsupported "condition" tm;

(* Splits off the top-level conjunct m.PC = A, if any *)
fun split_pc m body = let
  fun is_pc_eq c =
    is_eq c andalso aconv (lhs c) (mk_comb (PC_tm, m))
  val (pcs, rest) = partition is_pc_eq (strip_conj body)
  val pc_addr = case pcs of
      [] => NONE
    | [c] => let val a = rhs c in
        if null (free_vars a) andalso type_of a = word64_ty then SOME a
        else unsupported "PC address" a end
    | _ => raise ERR "arm8_cond_to_bir" "more than one PC conjunct"
  val q = if null rest then T else list_mk_conj rest
in (pc_addr, q) end;

(* ------------------ *)
(* Expression lifting *)
(* ------------------ *)

(* Lifts free word variables, like elf_literal_imm lifts literals *)
val elf_var_imm = let
  fun is_imm_var tm = let
    val tm' = if is_BLV_Imm tm then dest_BLV_Imm tm else tm
  in is_var (rand tm') end handle HOL_ERR _ => false
in
  elf_add_check (hd (elfs_of_thms [] [bir_is_lifted_imm_exp_CONSTANT]))
    (K is_imm_var)
end;

(* Rewrites before lifting: the comparisons not directly covered by
   bir_exp_liftingLib, and ==>, which it lifts as BIExp_LessOrEqual on
   Bit1 values. The latter is correct, but symbolic transfer's typing
   tactic for postconditions (in bir_symb_transfer_thm) can't show that
   such expressions are bool, and ~a \/ b is also easier to read *)
val preprocess_thms =
  [WORD_GREATER, WORD_GREATER_EQ, WORD_HIGHER, WORD_HIGHER_EQ,
   IMP_DISJ_THM];

fun lift_cond bs m q = let
  val bmr_tm = ``bmr_rel arm8_bmr ^bs ^m``
  val eln = eln_insert
    (eln_add_thms eln_default [bs, m] [SPECL [bs, m] arm8_bmr_LIFTED])
    elf_var_imm
  val q_eq = QCONV (PURE_REWRITE_CONV preprocess_thms) q
  val env_t = ``^bs.bst_environ``
  val th = bir_exp_lift env_t eln (mk_comb (``bool2b``, rhs (concl q_eq)))
  val _ = if is_bir_is_lifted_exp (concl th) andalso
             List.all (aconv bmr_tm) (hyp th) then ()
          else raise ERR "arm8_cond_to_bir"
            ("lifting left side conditions:\n" ^ thm_to_string th)
  val th1 = REWRITE_RULE [bir_is_lifted_exp_def] th
  val th1 = if aconv q (rhs (concl q_eq)) then th1
            else PURE_ONCE_REWRITE_RULE [GSYM q_eq] th1
in
  GENL [bs, m] (DISCH bmr_tm th1)
end;

(* ----------- *)
(* Translation *)
(* ----------- *)

fun bspec_name c_name =
  if String.isPrefix "arm8_" c_name
  then "bspec_" ^ String.extract (c_name, 5, NONE)
  else "bspec_" ^ c_name;

(* From |- !x1 ... xn m. c x1 ... xn m = body:
   (c, [x1, ..., xn], m, body) *)
fun dest_cond_def def = let
  val (l, body) = dest_eq (concl (SPEC_ALL def))
    handle HOL_ERR _ => raise ERR "arm8_cond_to_bir" "not an equation"
  val (c, args) = strip_comb l
  val _ = if is_const c andalso not (null args) andalso
             List.all is_var args andalso
             length (op_mk_set aconv args) = length args andalso
             type_of (last args) = arm8_state_ty andalso
             type_of body = bool
          then () else raise ERR "arm8_cond_to_bir"
            ("expected c x1 ... xn (m:arm8_state) = <bool>: " ^ term_to_string l)
in (c, butlast args, last args, body) end;

(* Everything up to the definition of the BIR constant, without side
   effects: the lifting theorem for the BIR expression e itself *)
fun lift_arm8_cond def = let
  val (c, params, m, body) = dest_cond_def def
  val (pc_addr, q) = split_pc m body
  val _ = if aconv q T then () else check_bool params m q
  val bs = variant (m :: params) ``bs:bir_state_t``
  val lifted = lift_cond bs m q
  val e = (rand o rator o snd o strip_imp o snd o strip_forall o concl) lifted
in (c, params, m, pc_addr, q, e, lifted) end;

(* The only side effect of the translation, done last so that a failing
   translation leaves the current theory unchanged. Returns the definition
   and a function folding the BIR expression into the new constant *)
fun define_bspec c params e = let
  val name = bspec_name (fst (dest_const c))
  val b_var = mk_var (name, list_mk_fun (map type_of params, type_of e))
  val bir_def = new_definition (name ^ "_def",
    mk_eq (list_mk_comb (b_var, params), e))
  (* as for Definition, so that EVAL (e.g. in symbolic execution) unfolds it,
     also in descendant theories *)
  val _ = computeLib.add_persistent_funs [name ^ "_def"]
in (bir_def, SUBS [SYM (SPECL params bir_def)]) end;

fun arm8_cond_to_bir def = let
  val (c, params, _, pc_addr, _, e, lifted) = lift_arm8_cond def
  val (bir_def, fold) = define_bspec c params e
in
  { bir_def = bir_def, lifted_thm = fold lifted, pc_addr = pc_addr }
end;

(* Instantiates a bridge lemma from arm8_bir_condTheory and discharges
   its premises other than the lifting judgment *)
fun bridge lemma insts lifted_thm def = let
  val th0 = BETA_RULE (ISPECL insts lemma)
  fun discharge th =
    if not (is_imp (concl th)) then th else let
      val prem = fst (dest_imp (concl th))
      val pth =
        if aconv prem (concl lifted_thm) then lifted_thm
        else if is_bir_is_bool_exp prem then prove (prem,
          SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
            [bir_is_bool_exp_def, bir_typing_expTheory.type_of_bir_exp_def,
             bir_valuesTheory.BType_Bool_def])
        else prove (prem,
          GEN_TAC >> REWRITE_TAC (def :: preprocess_thms) >> tautLib.TAUT_TAC)
    in discharge (MP th pth) end
in discharge th0 end;

(* Proves the relation theorem for the BIR expression with mk_rel_thm,
   then defines the BIR constant and folds it into the theorem *)
fun translate_with mk_rel_thm def = let
  val (c, params, m, pc_addr, q, e, lifted) = lift_arm8_cond def
  val p = list_mk_comb (c, params)
  val rel_thm = mk_rel_thm (p, mk_abs (m, q), e, pc_addr, lifted)
  val (bir_def, fold) = define_bspec c params e
in (bir_def, fold rel_thm) end;

fun arm8_pre_to_bir def = translate_with (fn (p, q, e, _, lifted) =>
    bridge bir_pre_arm8_to_bir_lifted [p, q, e] lifted def)
  def;

fun arm8_post_to_bir def = let
  val ls = mk_var ("ls", ``:bir_label_t -> bool``)
in
  translate_with (fn (p, q, e, pc_addr, lifted) =>
    GEN ls (case pc_addr of
        NONE => bridge bir_post_bir_to_arm8_lifted [p, q, e, ls] lifted def
      | SOME a => bridge bir_post_bir_to_arm8_lifted_PC [p, q, a, e, ls]
                    lifted def))
  def
end;

end
