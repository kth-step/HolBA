structure bir_exp_liftingLib :> bir_exp_liftingLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_liftingTheory


(**********)
(* Syntax *)
(**********)

val ERR = mk_HOL_ERR "bir_exp_lifting"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp_lifting"

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;


fun mk_bir_lift_val_t (ty1, ty2) =
   Type.mk_thy_type {Tyop = "bir_lift_val_t", Thy = "bir_exp_lifting", Args = [ty1, ty2]};

fun dest_bir_lift_val_t ty =
   case total dest_thy_type ty of
      SOME{Tyop = "bir_lift_val_t", Thy = "bir_exp_lifting", Args = [ty1, ty2]} => (ty1, ty2)
    | other => raise ERR "dest_bir_lift_val_t" "Invalid argument.";

val is_bir_lift_val_t = can dest_bir_lift_val_t;


val (bir_is_lifted_exp_tm, mk_bir_is_lifted_exp, dest_bir_is_lifted_exp, is_bir_is_lifted_exp)  = syntax_fns3 "bir_is_lifted_exp";

val (BLV_Imm_tm, mk_BLV_Imm, dest_BLV_Imm, is_BLV_Imm) = syntax_fns1 "BLV_Imm";
val (BLV_Mem_tm, mk_BLV_Mem, dest_BLV_Mem, is_BLV_Mem) = syntax_fns1 "BLV_Mem";

fun gen_mk_BLV t =
  mk_BLV_Imm (bir_immSyntax.gen_mk_Imm t) handle HOL_ERR _ =>
  mk_BLV_Mem t handle HOL_ERR _ =>
  mk_BLV_Imm t handle HOL_ERR _ =>
  raise (ERR "gen_mk_BLV" "");


(****************)
(* Prepare THMS *)
(****************)

(* Brings theorems for lifting expressions into canonical form.
   In canonical form, they have a set of assumptions.
   The body is a single bir_is_lifted_exp.
   The variables in the conclusion are all freshly generated, such that
   there won't be undesired effects while matching.

   prepare_exp_lifting_thm is able to split theorems on conjunctions, strip implications and
   universal quantification. It uses bir_is_lifted_exp_INTRO to
   introduce bir_is_lifted_exp theorem. It returns a set of theorems. *)

(* DEBUG
 val thm = bir_is_lifted_imm_exp_UNARY_EXP
*)

local

  val intro_bir_is_lifted_exp  = PURE_REWRITE_RULE [bir_is_lifted_exp_INTRO]

  fun base_thms thm =
    if is_forall (concl thm)
      then base_thms (SPEC_ALL thm)
    else if is_conj (concl thm)
      then (base_thms (CONJUNCT1 thm) @ base_thms (CONJUNCT2 thm))
    else if is_imp_only (concl thm)
      then base_thms (UNDISCH thm)
    else [thm];

  fun fresh_vars fixed_vars thm =
  let
    val fvs' = FVL (concl thm::hyp thm) empty_tmset
    val fvs = HOLset.difference (fvs', HOLset.addList (empty_tmset, fixed_vars))
    val fvl = HOLset.listItems fvs
    val vs = map (fn v => (v |-> genvar (type_of v))) fvl
    val thm1 = INST vs thm;

    val tvl = type_vars_in_term (concl thm1)
    val tys = map (fn v => (v |-> gen_tyvar ())) tvl
    val thm2 = INST_TYPE tys thm1
  in thm2 end;

  val filter_thms = filter (fn thm => is_bir_is_lifted_exp (concl thm))
in

fun prepare_exp_lifting_thm fixed_vars thm =
  map (fresh_vars fixed_vars) (filter_thms (base_thms (intro_bir_is_lifted_exp thm)));

fun prepare_exp_lifting_thms fixed_vars thms = flatten (map (prepare_exp_lifting_thm fixed_vars) thms)

end


(******************)
(* Datastructures *)
(******************)

(* We need a datastructure for storing lifting theorems together with some meta-data.
   At top-level, we need to be able to instantiate a theorem, given an immediate and an
   environment. This can succeed or fail (i.e. raise a HOL_ERR exception). For efficiency
   we also want an enabling pattern to quickly discard not needed cases. Finally, we want
   a precedence number to be able to process possible tries in a decent order. *)

type exp_lifting_fun_rec = {
   elf_mk_exp_lift_thm : term -> term -> thm,
   elf_guard           : term,
   elf_checks          : (term -> term -> bool) list,
   elf_precedence      : int
};

val elf_precedence_high    = 5;
val elf_precedence_default = 10;
val elf_precedence_low     = 15;


fun mk_elf (guard_opt : term option) (mk_f : term (*env*) -> term (*value*) -> thm) = {
   elf_mk_exp_lift_thm = mk_f,
   elf_guard           = case guard_opt of SOME guard => guard | NONE => genvar (mk_bir_lift_val_t (Type.alpha, Type.beta)),
   elf_checks          = [],
   elf_precedence      = elf_precedence_default
}:exp_lifting_fun_rec;


fun elf_set_precedence (r : exp_lifting_fun_rec) pr = {
   elf_mk_exp_lift_thm = #elf_mk_exp_lift_thm r,
   elf_guard           = #elf_guard r,
   elf_checks          = #elf_checks r,
   elf_precedence      = pr
}:exp_lifting_fun_rec;


fun elf_add_check (r : exp_lifting_fun_rec) (gf : term -> term -> bool) = {
   elf_mk_exp_lift_thm = #elf_mk_exp_lift_thm r,
   elf_guard           = #elf_guard r,
   elf_checks          = gf :: (#elf_checks r),
   elf_precedence      = #elf_precedence r
}:exp_lifting_fun_rec;


fun elf_apply (r : exp_lifting_fun_rec) env_t v_t = let
  val gc = List.all (fn gf => (gf env_t v_t) handle HOL_ERR _ => false) (#elf_checks r)
  val _ = if gc then () else failwith "Guards violated";

  val thm0 = #elf_mk_exp_lift_thm r env_t v_t;
in
  thm0
end;









(* The most common ones are constructed from theorems as above. So we need a special
   datatype for such theorems and a conversion to type exp_lifting_fun_rec *)

type exp_lifting_thm_rec = {
   elt_thm        : thm,
   elt_fresh_vars : term list, (* Vars that need to be freshly generated for each instance *)
   elt_guard      : term,
   elt_env        : term
};


(* DEBUG values
val thms = prepare_exp_lifting_thms [] [bir_is_lifted_imm_exp_BIN_EXP]
val thm = hd thms
fun gf _ _ = true
*)

fun mk_exp_lifting_thm_rec_from_thm thm = let
  val (env, et, vt) = dest_bir_is_lifted_exp (concl thm)
  val fvl = HOLset.listItems (HOLset.difference (FVL [et] empty_tmset,
      FVL [vt, env] empty_tmset))

in {
   elt_thm       = thm,
   elt_fresh_vars= fvl,
   elt_guard     = vt,
   elt_env       = env
  }:exp_lifting_thm_rec
end;


(*
DEBUG VALUES:

val r = mk_exp_lifting_thm_rec_from_thm (el 45 thms)
val env_t = ``env:bir_var_environment_t``
val vt = ``BLV_Imm (Imm32 (5w * w))``
*)


fun exp_lifting_thm_rec_match (r:exp_lifting_thm_rec) env_t vt =
let
  val (tm_s, ty_s) = match_term (#elt_guard r) vt
  val _ = if (exists (fn r => not (is_genvar (#redex r))) tm_s) then fail() else ()
  val thm0 = INST tm_s (INST_TYPE ty_s (#elt_thm r))

  val (tm_s', ty_s') = match_term (subst tm_s (inst ty_s (#elt_env r))) env_t
  val _ = if (exists (fn r => not (is_genvar (#redex r))) tm_s') then fail() else ()
  val thm1 = INST tm_s' (INST_TYPE ty_s' thm0)

  (* introduce fresh vars *)
  val vs = map (fn v => (v |-> genvar (type_of v))) (#elt_fresh_vars r)
  val thm2 = INST vs thm1
in
  thm2
end;


fun exp_lifting_thm_rec_2_fun_rec r = mk_elf (SOME (#elt_guard r)) (exp_lifting_thm_rec_match r);


fun elfs_of_thms fixed_vars thms = map (exp_lifting_thm_rec_2_fun_rec o mk_exp_lifting_thm_rec_from_thm) (prepare_exp_lifting_thms fixed_vars thms);



(**************************************)
(* Term nets                          *)
(**************************************)

(* for efficiency we put exp_lifting_fun_rec into a term net. *)

type exp_lifting_net = exp_lifting_fun_rec Net.net

val eln_empty = Net.empty:exp_lifting_net;

fun eln_insert (n:exp_lifting_net) (r:exp_lifting_fun_rec) : exp_lifting_net =
  Net.insert (#elf_guard r, r) n;

fun eln_list_insert (n:exp_lifting_net) (rs : exp_lifting_fun_rec list) : exp_lifting_net =
  foldl (fn (r, n) => eln_insert n r) n rs;

fun eln_of_elfs rs = eln_list_insert eln_empty rs

fun eln_union (n1:exp_lifting_net) (n2:exp_lifting_net) : exp_lifting_net =
  Net.union n1 n2;

fun eln_add_thms ne fixed_vars thms =
  eln_list_insert ne (elfs_of_thms fixed_vars thms);

fun eln_add_thms_with_precedence ne pr fixed_vars thms = let
  val rl = elfs_of_thms fixed_vars thms;
  val rl' = map (fn r => elf_set_precedence r pr) rl
in
  eln_list_insert ne rl'
end;

val eln_of_thms = eln_add_thms eln_empty;


(* DEBUG VALUES

val thms = [bir_is_lifted_exp_BIN_EXP, bir_is_lifted_exp_UNARY_EXP, bir_is_lifted_exp_CONSTANT];
val n = eln_union (eln_from_thms 5 thms) (eln_from_thms 1 thms)

val n = eln_from_thms 5 [bir_is_lifted_exp_CONSTANT]

val tm = ``BVal_Imm (Imm32 ((5w * w) + w2))``
val env = ``envxxx : bir_var_environment_t``
*)

fun eln_match (n:exp_lifting_net) tm = let
  val rs = Net.match tm n;
  val rs' = sort (fn r1 => fn r2 => (#elf_precedence r1 < #elf_precedence r2)) rs
in
  rs'
end;


fun eln_apply n env tm = let
  val rs = eln_match n tm;
in
  Lib.tryfind (fn r => (elf_apply r env tm)) rs
end


(****************************************)
(* Lifting literals                     *)
(****************************************)

(* When lifting literals one needs to be careful. The theorem
   bir_is_lifted_exp_CONSTANT is powerful enough to lift any
   immediate expression trivially. To get useful results, we need
   to restrict it's usage to cases, where the immediate value is
   really a constant *)

(* DEBUG

val tm = ``(BVal_Imm (Imm32 5w))``
val tm = ``(BVal_Imm (Imm1 w))``
*)

fun bir_is_imm_literal tm = let
  val tm' = dest_BLV_Imm tm;
  val (_, w) = bir_immSyntax.gen_dest_Imm tm'
in
  wordsSyntax.is_n2w w
end handle HOL_ERR _ => false;


val elf_literal_imm = let
  val rl = elfs_of_thms [] [bir_is_lifted_imm_exp_CONSTANT]
  val _ = assert (fn () => length rl = 1) ()
  val r = elf_add_check (hd rl) (K bir_is_imm_literal)
in r end;


val eln_default = let
  val eln = eln_of_thms [] [bir_is_lifted_imm_exp_DEFAULT_THMS]
  val eln = eln_insert eln elf_literal_imm
in
  eln
end;


(**************************************)
(* Caches                             *)
(**************************************)

(* During the lifting of one expression, we want to reuse already performed
   liftings. This prevents multiple occurrences of the same subexpression to be
   lifted multiple times, causing unnecessary lengthy and complicated results. *)
type exp_lifting_cache = thm Net.net

val elc_empty = Net.empty:exp_lifting_cache;

fun elc_insert thm (c:exp_lifting_cache) : exp_lifting_cache = let
  val (_, _, vt) = dest_bir_is_lifted_exp (concl thm)
in
  Net.insert (vt, thm) c
end handle HOL_ERR _ => c;


fun elc_apply (c:exp_lifting_cache) env tm = let
  val rs = Net.index tm c;
  fun check thm = let
    val (env', et', vt') = dest_bir_is_lifted_exp (concl thm)
    val _ = if (aconv tm vt') then () else fail();
    val _ = if (aconv env env') then () else fail();
  in
    (thm, et')
  end;
in
  Lib.tryfind check rs
end

(* DEBUG VALUES

val c = elc_empty
val thm = mthm
  val (c', mthm') = elc_process_thm c mthm

*)


fun elc_process_thm (c:exp_lifting_cache) thm = let
  fun process_hyp (h, (ch, c, thm)) = let
    val (env_t, ev, vt) = dest_bir_is_lifted_exp h
    val (thm_h, ev') = elc_apply c env_t vt
  in if (aconv ev ev') then (ch, c, thm) else let
    val thm0 = INST [ev |-> ev'] thm
    val thm1 = PROVE_HYP thm_h thm0
  in
    (true, c, thm1)
  end end handle HOL_ERR _ => (ch, elc_insert (ASSUME h) c, thm);

  val (ch, c0, thm') = foldl process_hyp (false, c, thm) (hyp thm)

  val (c1, thm'') = if ch then elc_process_thm c0 thm' else (c0, thm')
  val c2 = Net.delete (concl thm'', K true) c1
  val c3 = elc_insert thm'' c2
in
  (c3, thm'')
end;



(****************************************)
(* Lifting                              *)
(****************************************)

(* Now we combine everything to get the real lifting *)

fun bir_exp_lift_init env_t vt =
  ASSUME (mk_bir_is_lifted_exp (env_t, genvar bir_expSyntax.bir_exp_t_ty, gen_mk_BLV vt))


(* DEBUG

val env_t = ``env : bir_var_environment_t``
val vt = ``Imm32 (5w * w + w)``

val thms = [bir_is_lifted_imm_exp_BIN_EXP, bir_is_lifted_imm_exp_UNARY_EXP];
val n = eln_empty
val n = eln_from_thms 5 thms
val n = eln_insert_thm_rec 5 literal_imm_exp_lifting_thm_rec n

val thm = mk_initial_is_lifted_imm_exp_thm env_t vt
val tm = hd (hyp thm)
val c = elc_empty
*)

fun bir_exp_lift_step (c : exp_lifting_cache) (n:exp_lifting_net) thm tm = let
  val (env_t, et, vt) = dest_bir_is_lifted_exp tm
  val mthm = eln_apply n env_t vt
  val (env_t', et', vt') = dest_bir_is_lifted_exp (concl mthm)

  (* Safety checks *)
  val _ = assert (aconv env_t) env_t'
  val _ = assert (aconv vt) vt'

  val thm1 = INST [et |-> et'] thm
  val thm2 = PROVE_HYP mthm thm1

  val (c', thm3) = elc_process_thm c thm2

in
  (c', thm3)
end ;

fun bir_exp_lift_continue n (c, thm) = let
  val thm_opt = total (tryfind (bir_exp_lift_step c n thm)) (hyp thm);
in
  case thm_opt of NONE => (c, thm)
                | SOME (c', thm') => bir_exp_lift_continue n (c', thm')
end;

fun bir_exp_lift_final thm = let
  val thm0 = let
     val lift_hyps = filter is_bir_is_lifted_exp (hyp thm)
  in foldl (uncurry DISCH) thm lift_hyps end;
  val vars = filter (fn v => is_genvar v andalso (type_of v = bir_expSyntax.bir_exp_t_ty)) (free_vars (concl thm0))

  fun gen_newname uvs c = let
     val v = mk_var ("e"^(int_to_string c), bir_expSyntax.bir_exp_t_ty)
  in if (holba_eq_utilLib.mem_with (fn (a,b) => identical a b) v uvs) then gen_newname uvs (c + 1) else (v::uvs, c, v) end;

  val (s, _, _) = foldl (fn (gv, (s, uvs, c)) => let
    val (uvs', c', v) = gen_newname uvs c
    val s' = (gv |-> v) :: s
  in (s', uvs', c') end) ([], all_vars (concl thm), 1) vars

   val thm1 = INST s thm0
in
  thm1
end;

fun bir_exp_lift env_t n tm = let
  val init_thm = bir_exp_lift_init env_t tm;
  val (_, res_thm) = bir_exp_lift_continue n (elc_empty, init_thm);
  val final_thm = bir_exp_lift_final res_thm
in
  final_thm
end;


val bir_var_environment_t_default = ``env : bir_var_environment_t``;
val bir_exp_lift_default_env = bir_exp_lift bir_var_environment_t_default;



(* DEBUGGING

val env_t = bir_var_environment_t_default

val n = eln_default
val n = eln_empty
val n = eln_of_thms thms
val n = eln_insert n elf_literal_imm
(* From exp_lift_fn_raw: *)
(*
   val env_t = mk_bst_environ bs_v
   val n = eln2
*)


bir_exp_lift env_t n ``(Imm32 (5w * w + w - 3w * w2 // (w + w2)))``

bir_exp_lift env_t n ``(5w * w + w - 3w * w2 // (w + w2)):word32``
bir_exp_lift env_t n ``(5w * w + w - 3w * w2 // (w + w2)):word8``

bir_exp_lift env_t n ``(Imm32 5w)``
bir_exp_lift env_t n ``(Imm32 (5w + 3w))``
bir_exp_lift env_t n ``(Imm32 (5w + w1))``
bir_exp_lift env_t n ``(Imm1 (5w + w1))``


bir_exp_lift env_t n ``(Imm1 (w1 + w1 + w1))``
bir_exp_lift env_t n ``(Imm1 (w1 + w1 + w1 // w2))``

bir_exp_lift env_t n ``(Imm1 (w2w (7w:word8)))``
bir_exp_lift env_t n ``(Imm8 (w2w (7w:word8)))``
bir_exp_lift env_t n ``(Imm16 (w2w (7w:word8)))``
bir_exp_lift env_t n ``(Imm16 (sw2sw (7w:word8)))``
bir_exp_lift env_t n ``Imm32 (w2w ((v2w [F; F; F; F; T; F; F]):word8))``
bir_exp_lift env_t n ``Imm32 (w2w ((v2w [F; F; F; F; T; F; F]):word7))``

bir_exp_lift env_t n ``(w1:word32 < w2) /\ (w2 < w3)``
bir_exp_lift env_t n ``(w1:word32 < w2) \/ (w2 < w3)``
bir_exp_lift env_t n ``(w1:word32 < w2) ==> (w2 < w3)``


bir_exp_lift env_t n ``aligned 3 ((0x1000w:word16) + x)``
bir_exp_lift env_t n ``if (w1:word32 < w2) then 0w:word16 else 16w``

bir_exp_lift env_t n ``Imm32((((mem:word32 -> word8)
                  (b +
                   (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32)) @@
                ((mem
                    (b +
                     (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                     (1w :word32)) @@
                 ((mem
                     (b +
                      (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                      (2w :word32)) @@
                  mem
                    (b +
                     (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                     (3w :word32)))
                    :word16))
                   :word24))
                 :word32) + ((mem:word32 -> word8)
                  (b2 +
                   (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32)) @@
                ((mem
                    (b2 +
                     (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                     (1w :word32)) @@
                 ((mem
                     (b2 +
                      (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                      (2w :word32)) @@
                  mem
                    (b2 +
                     (w2w (v2w [F; F; F; F; T; F; F] :word7) :word32) +
                     (3w :word32)))
                    :word16))
                   :word24))
                 :word32)``;

bir_exp_lift env_t n ``Imm64
                (w2w
                   (ExtendValue (w2w (ms.REG 12w),ExtendType_SXTB,0) +
                    w2w (ms.REG 15w)))``

*)

end
