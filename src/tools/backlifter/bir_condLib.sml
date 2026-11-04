structure bir_condLib :> bir_condLib =
struct

open HolKernel boolLib Parse bossLib;

open wordsTheory;
open bir_bool_expTheory bir_expTheory;
open bir_exp_liftingTheory bir_lifting_machinesTheory;
open bir_exp_liftingLib;

val is_bir_is_bool_exp = can (match_term ``bir_is_bool_exp e``);

type arch_info =
  { arch            : string,
    state_ty        : hol_type,
    bmr             : term,
    bmr_lifted      : thm,
    dest_load       : term -> term -> term option,
    pc_of           : term -> term,
    load_thms       : thm list,
    pre_lifted      : thm,
    post_lifted     : thm,
    post_lifted_PC  : thm,
    post_cases_nil  : thm,
    post_cases_cons : thm }

type bir_cond_result =
  { bir_def    : thm,
    lifted_thm : thm,
    pc_addr    : term option }

fun ERR (a : arch_info) f msg =
  mk_HOL_ERR (#arch a ^ "_bir_condLib") (#arch a ^ "_" ^ f) msg;

(* ------------------ *)
(* Supported fragment *)
(* ------------------ *)

val word64_ty = wordsSyntax.mk_int_word_type 64;

fun unsupported a what tm =
  raise ERR a "cond_to_bir"
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
  ``word_and``, ``word_or``, ``word_xor``,
  ``word_lsl_bv``, ``word_lsr_bv``, ``word_asr_bv``];

(* The state reads of m that the architecture's lifting theorem lifts to
   BIR variables, e.g. m.REG 0w or (m.c_MCSR m.procID).mscratch, some as
   casts, e.g. w2w (m.c_MCSR m.procID).mstatus.MPRV *)
fun state_reads (a : arch_info) m = let
  val bs = variant [m] ``bs:bir_state_t``
  val lifted = (snd o dest_imp o concl o SPECL [bs, m]) (#bmr_lifted a)
  fun read c = let
    val v = rand c
  in if is_BLV_Imm v then SOME (rand (dest_BLV_Imm v)) else NONE end
    handle HOL_ERR _ => NONE
in List.mapPartial read (strip_conj lifted) end;

(* Words built with the operations above from state reads, loads from
   such words, free variables among the parameters, and literals *)
fun check_word (a : arch_info) reads params m tm =
  if tmem tm reads then ()
  else if not (is_supported_word_ty (type_of tm)) then
    unsupported a "word type" tm
  else if wordsSyntax.is_word_literal tm then ()
  else if is_var tm then
    (if tmem tm params then () else unsupported a "free variable" tm)
  else case #dest_load a m tm of
    SOME addr => check_word a reads params m addr
  | NONE => let
      val (f, args) = strip_comb tm
      fun is_op ops = is_const f andalso exists (same_const f) ops
    in
      case args of
        [x] =>
          if is_op word_unops then check_word a reads params m x
          else unsupported a "word term" tm
      | [x, y] =>
          if is_op word_binops then
            (check_word a reads params m x; check_word a reads params m y)
          else unsupported a "word term" tm
      | _ => unsupported a "word term" tm
    end;

val word_preds = [
  wordsSyntax.dest_word_lo, wordsSyntax.dest_word_ls,
  wordsSyntax.dest_word_hi, wordsSyntax.dest_word_hs,
  wordsSyntax.dest_word_lt, wordsSyntax.dest_word_le,
  wordsSyntax.dest_word_gt, wordsSyntax.dest_word_ge];

fun check_bool a reads params m tm =
  if is_conj tm orelse is_disj tm orelse is_imp_only tm then
    let val (x, y) = dest_comb tm |> (fn (l, r) => (rand l, r))
    in (check_bool a reads params m x; check_bool a reads params m y) end
  else if is_neg tm then check_bool a reads params m (dest_neg tm)
  else if is_eq tm then let
    val (x, y) = dest_eq tm
  in (check_word a reads params m x; check_word a reads params m y) end
  else case List.mapPartial (fn d => SOME (d tm) handle HOL_ERR _ => NONE) word_preds of
    [(x, y)] => (check_word a reads params m x; check_word a reads params m y)
  | _ => unsupported a "condition" tm;

fun check_pc_addr a addr =
  if null (free_vars addr) andalso type_of addr = word64_ty then ()
  else unsupported a "PC address" addr;

(* Splits off the top-level conjunct PC = A, if any *)
fun split_pc (a : arch_info) m body = let
  fun is_pc_eq c = is_eq c andalso aconv (lhs c) (#pc_of a m)
  val (pcs, rest) = partition is_pc_eq (strip_conj body)
  val pc_addr = case pcs of
      [] => NONE
    | [c] => (check_pc_addr a (rhs c); SOME (rhs c))
    | _ => raise ERR a "cond_to_bir" "more than one PC conjunct"
  val q = if null rest then T else list_mk_conj rest
in (pc_addr, q) end;

(* ------------- *)
(* Normalization *)
(* ------------- *)

(* Before the fragment check: closed word terms that are not literals,
   e.g. address constants such as kernel_trap_slots_addr or
   init_addr - 256w, are evaluated to literals, so that the BIR
   expression has literal constants that the SMT translation can use *)
fun closed_words_conv tm =
  if wordsSyntax.is_word_type (type_of tm) andalso null (free_vars tm) andalso
     not (wordsSyntax.is_word_literal tm)
  then let
    val th = EVAL tm
  in if wordsSyntax.is_word_literal (rhs (concl th)) then th else ALL_CONV tm end
  else SUB_CONV closed_words_conv tm;

(* Narrow state components that are lifted only as a cast w2w t to a
   wider word, e.g. the 2-bit (m.c_MCSR m.procID).mstatus.MPRV, lifted as
   w2w ... : word8: an equation t = c or c = t with a literal c becomes
   w2w t = c' or c' = w2w t, with c' the literal w2w c. w2w is injective
   on such widening casts *)
fun narrow_eq_conv reads tm = let
  fun widened t = List.find (fn r =>
      wordsSyntax.is_w2w r andalso aconv (fst (wordsSyntax.dest_w2w r)) t)
    reads
  fun rule t c r flip = let
    val wide_ty = type_of r
    val c' = rhs (concl (EVAL (wordsSyntax.mk_w2w (c, wordsSyntax.dest_word_type wide_ty))))
    val x = genvar (type_of t)
    val (l1, l2) = if flip then (mk_eq (c, x), mk_eq (c', subst [t |-> x] r))
                   else (mk_eq (x, c), mk_eq (subst [t |-> x] r, c'))
    val th = blastLib.BBLAST_PROVE (mk_forall (x, mk_eq (l1, l2)))
  in SPEC t th end
in
  if is_eq tm andalso wordsSyntax.is_word_type (type_of (lhs tm)) then let
    val (l, r) = dest_eq tm
  in
    case (widened l, widened r) of
      (SOME w, _) =>
        if wordsSyntax.is_word_literal r then rule l r w false else ALL_CONV tm
    | (NONE, SOME w) =>
        if wordsSyntax.is_word_literal l then rule r l w true else ALL_CONV tm
    | _ => ALL_CONV tm
  end
  else SUB_CONV (narrow_eq_conv reads) tm
end;

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
   such expressions are bool, and ~a \/ b is also easier to read.
   The architecture's load_thms unfold loads to the byte concatenation
   that bir_exp_liftingLib lifts to a little-endian BExp_Load *)
fun preprocess_thms (a : arch_info) =
  [WORD_GREATER, WORD_GREATER_EQ, WORD_HIGHER, WORD_HIGHER_EQ,
   IMP_DISJ_THM] @ #load_thms a;

fun lift_cond (a : arch_info) bs m q = let
  val bmr_tm = ``bmr_rel ^(#bmr a) ^bs ^m``
  val eln = eln_insert
    (eln_add_thms eln_default [bs, m] [SPECL [bs, m] (#bmr_lifted a)])
    elf_var_imm
  val q_eq = QCONV (PURE_REWRITE_CONV (preprocess_thms a)) q
  val env_t = ``^bs.bst_environ``
  val th = bir_exp_lift env_t eln (mk_comb (``bool2b``, rhs (concl q_eq)))
  val _ = if is_bir_is_lifted_exp (concl th) andalso
             List.all (aconv bmr_tm) (hyp th) then ()
          else raise ERR a "cond_to_bir"
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

fun bspec_name (a : arch_info) c_name = let
  val prefix = #arch a ^ "_"
in
  if String.isPrefix prefix c_name
  then "bspec_" ^ String.extract (c_name, size prefix, NONE)
  else "bspec_" ^ c_name
end;

(* From |- !x1 ... xn m. c x1 ... xn m = body:
   (c, [x1, ..., xn], m, body) *)
fun dest_cond_def (a : arch_info) def = let
  val (l, body) = dest_eq (concl (SPEC_ALL def))
    handle HOL_ERR _ => raise ERR a "cond_to_bir" "not an equation"
  val (c, args) = strip_comb l
  val _ = if is_const c andalso not (null args) andalso
             List.all is_var args andalso
             length (op_mk_set aconv args) = length args andalso
             type_of (last args) = #state_ty a andalso
             type_of body = bool
          then () else raise ERR a "cond_to_bir"
            ("expected c x1 ... xn (m:" ^ type_to_string (#state_ty a) ^
             ") = <bool>: " ^ term_to_string l)
in (c, butlast args, last args, body) end;

(* Everything up to the definition of the BIR constant, without side
   effects: the lifting theorem for the BIR expression e itself *)
fun lift_def_cond a def = let
  val (c, params, m, body) = dest_cond_def a def
  val (pc_addr, q) = split_pc a m body
  val reads = state_reads a m
  val norm_eq = QCONV (closed_words_conv THENC narrow_eq_conv reads) q
  val q1 = rhs (concl norm_eq)
  val _ = if aconv q1 T then () else check_bool a reads params m q1
  val bs = variant (m :: params) ``bs:bir_state_t``
  val lifted = lift_cond a bs m q1
  val lifted = if aconv q q1 then lifted
               else GENL [bs, m] (PURE_ONCE_REWRITE_RULE [GSYM norm_eq]
                                    (SPECL [bs, m] lifted))
  val e = (rand o rator o snd o strip_imp o snd o strip_forall o concl) lifted
in (c, params, m, pc_addr, q, e, lifted) end;

(* The only side effect of the translation, done last so that a failing
   translation leaves the current theory unchanged. Returns the definition
   and a function folding the BIR expression into the new constant *)
fun define_bspec a c params e = let
  val name = bspec_name a (fst (dest_const c))
  val b_var = mk_var (name, list_mk_fun (map type_of params, type_of e))
  val bir_def = new_definition (name ^ "_def",
    mk_eq (list_mk_comb (b_var, params), e))
  (* as for Definition, so that EVAL (e.g. in symbolic execution) unfolds it,
     also in descendant theories *)
  val _ = computeLib.add_persistent_funs [name ^ "_def"]
in (bir_def, SUBS [SYM (SPECL params bir_def)]) end;

fun cond_to_bir a def = let
  val (c, params, _, pc_addr, _, e, lifted) = lift_def_cond a def
  val (bir_def, fold) = define_bspec a c params e
in
  { bir_def = bir_def, lifted_thm = fold lifted, pc_addr = pc_addr }
end;

(* Instantiates a bridge lemma and discharges its premises other than the
   lifting judgment *)
fun bridge a lemma insts lifted_thm def = let
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
          GEN_TAC >> REWRITE_TAC (def :: preprocess_thms a) >>
          tautLib.TAUT_TAC)
    in discharge (MP th pth) end
in discharge th0 end;

(* Proves the relation theorem for the BIR expression with mk_rel_thm,
   then defines the BIR constant and folds it into the theorem *)
fun translate_with a mk_rel_thm def = let
  val (c, params, m, pc_addr, q, e, lifted) = lift_def_cond a def
  val p = list_mk_comb (c, params)
  val rel_thm = mk_rel_thm (p, mk_abs (m, q), e, pc_addr, lifted)
  val (bir_def, fold) = define_bspec a c params e
in (bir_def, fold rel_thm) end;

fun pre_to_bir a def = translate_with a (fn (p, q, e, _, lifted) =>
    bridge a (#pre_lifted a) [p, q, e] lifted def)
  def;

val ls_var = mk_var ("ls", ``:bir_label_t -> bool``);

fun post_to_bir a def =
  translate_with a (fn (p, q, e, pc_addr, lifted) =>
    GEN ls_var (case pc_addr of
        NONE => bridge a (#post_lifted a) [p, q, e, ls_var] lifted def
      | SOME addr => bridge a (#post_lifted_PC a) [p, q, addr, e, ls_var]
                       lifted def))
  def;

(* Postconditions by cases on the PC *)

(* From if PC = A1 then t1 else ... if PC = An then tn else F:
   [(A1, t1), ..., (An, tn)] *)
fun dest_pc_cases (a : arch_info) m tm =
  if aconv tm F then []
  else let
    val (c, t, rest) = dest_cond tm
      handle HOL_ERR _ => unsupported a "PC case" tm
    val addr = if is_eq c andalso aconv (lhs c) (#pc_of a m)
               then rhs c else unsupported a "PC case condition" c
    val _ = check_pc_addr a addr
  in (addr, t) :: dest_pc_cases a m rest end;

(* The lifting theorem of a case condition, stated for c y1 ... yk m
   instead of its body *)
fun fold_case_lifted def lifted =
  CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (RAND_CONV (RAND_CONV
    (REWR_CONV (GSYM (SPEC_ALL def))))))) lifted;

fun post_cases_to_bir a def case_defs = let
  val (c, params, m, body) = dest_cond_def a def
  val cases = dest_pc_cases a m body
  val _ = if null cases then unsupported a "postcondition by PC cases" body
          else ()
  (* each case condition must be a translatable condition without a PC
     conjunct, applied to terms over the parameters *)
  val lifts = map (fn d => let
      val (ci, ps, _, pc_addr, _, e, lifted) = lift_def_cond a d
      val _ = if isSome pc_addr then raise ERR a "post_cases_to_bir"
                ("PC conjunct in case condition " ^ fst (dest_const ci))
              else ()
    in (ci, (d, ps, e, fold_case_lifted d lifted)) end) case_defs
  fun lookup t = let
    val (ci, args) = strip_comb t
    val ys = butlast args
    val _ = if not (null args) andalso aconv (last args) m andalso
               List.all (fn y => List.all (fn v => tmem v params)
                 (free_vars y)) ys
            then () else unsupported a "PC case" t
  in case List.find (fn (cj, _) => aconv cj ci) lifts of
      SOME (_, (d, ps, e, lifted)) => let
        val s = map2 (curry op |->) ps ys
      in (ci, ys, subst s e, INST s lifted) end
    | NONE => unsupported a "PC case (no case definition given)" t
  end
  val cases' = map (fn (addr, t) => (addr, lookup t)) cases
  val _ = case List.find (fn (ci, _) =>
                not (exists (fn (_, (cj, _, _, _)) => aconv ci cj) cases'))
              lifts of
      NONE => ()
    | SOME (ci, _) => raise ERR a "post_cases_to_bir"
        ("case definition not used: " ^ fst (dest_const ci))
  val p_top = list_mk_comb (c, params)
  (* the relation theorem for the cases from the k-th on, with p the
     ISA postcondition to state it for *)
  fun rel p [] = SPEC ls_var (#post_cases_nil a)
    | rel p ((addr, (ci, ys, e, lifted)) :: rest) = let
        val tail_tm = foldr (fn ((addr', (cj, ys', _, _)), acc) =>
            mk_cond (mk_eq (#pc_of a m, addr'),
                     list_mk_comb (cj, ys' @ [m]), acc))
          F rest
        val r = mk_abs (m, tail_tm)
        val r_thm = rel r rest
        val f = (rand o rator o concl) r_thm
        val q = list_mk_comb (ci, ys)
        val th0 = BETA_RULE (ISPECL [p, q, r, addr, e, f, ls_var]
                    (#post_cases_cons a))
        val th1 = MP (MP th0 lifted) r_thm
        val prem = fst (dest_imp (concl th1))
      in MP th1 (prove (prem, GEN_TAC >> REWRITE_TAC [def])) end
  val rel_thm = GEN ls_var (rel p_top cases')
  (* only now define the BIR constants, once for each case definition,
     and fold them into the relation theorem *)
  val bir_defs = map (fn (ci, (_, ps, e, _)) =>
      (ci, fst (define_bspec a ci ps e))) lifts
  fun fold_case ((_, (ci, ys, _, _)), th) = let
    val bir_def = snd (valOf (List.find (fn (cj, _) => aconv ci cj) bir_defs))
  in SUBS [SYM (ISPECL ys bir_def)] th end
in (map snd bir_defs, foldl fold_case rel_thm cases') end;

end
