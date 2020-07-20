structure bir_immSyntax :> bir_immSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib bir_eq_utilLib;
open bir_immTheory;


val ERR = mk_HOL_ERR "bir_immSyntax"
val wrap_exn = Feedback.wrap_exn "bir_immSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_imm"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;



(* bir_immtype_t *)

val bir_immtype_t_ty = mk_type ("bir_immtype_t", []);
val bir_immtype_t_list = TypeBase.constructors_of bir_immtype_t_ty;
val _ = if ((length bir_immtype_t_list) = 6) then () else
    (failwith "number of bir_immtype_t constructors changed, please adapt")

val (Bit1_tm,   is_Bit1)   = syntax_fns0 "Bit1";
val (Bit8_tm,   is_Bit8)   = syntax_fns0 "Bit8";
val (Bit16_tm,  is_Bit16)  = syntax_fns0 "Bit16";
val (Bit32_tm,  is_Bit32)  = syntax_fns0 "Bit32";
val (Bit64_tm,  is_Bit64)  = syntax_fns0 "Bit64";
val (Bit128_tm, is_Bit128) = syntax_fns0 "Bit128";


(* bir_imm_t *)

val bir_imm_t_ty = mk_type ("bir_imm_t", []);
val bir_imm_t_list = TypeBase.constructors_of bir_imm_t_ty;

val _ = if ((length bir_imm_t_list) = (length bir_immtype_t_list)) then () else
    (failwith "number of bir_imm_t constructors changed, please adapt");


val (Imm1_tm,   mk_Imm1,   dest_Imm1,   is_Imm1)   = syntax_fns1 "Imm1";
val (Imm8_tm,   mk_Imm8,   dest_Imm8,   is_Imm8)   = syntax_fns1 "Imm8";
val (Imm16_tm,  mk_Imm16,  dest_Imm16,  is_Imm16)  = syntax_fns1 "Imm16";
val (Imm32_tm,  mk_Imm32,  dest_Imm32,  is_Imm32)  = syntax_fns1 "Imm32";
val (Imm64_tm,  mk_Imm64,  dest_Imm64,  is_Imm64)  = syntax_fns1 "Imm64";
val (Imm128_tm, mk_Imm128, dest_Imm128, is_Imm128) = syntax_fns1 "Imm128";



(* various functions *)

val (b2v_tm, mk_b2v, dest_b2v, is_b2v)  = syntax_fns1 "b2v";
val (v2bs_tm, mk_v2bs, dest_v2bs, is_v2bs)  = syntax_fns2 "v2bs";
val (bool2b_tm, mk_bool2b, dest_bool2b, is_bool2b)  = syntax_fns1 "bool2b";
val (w2bs_tm, mk_w2bs, dest_w2bs, is_w2bs)  = syntax_fns2 "w2bs";
val (b2w_tm, mk_b2w, dest_b2w, is_b2w)  = syntax_fns1 "b2w";
val (n2bs_tm, mk_n2bs, dest_n2bs, is_n2bs)  = syntax_fns2 "n2bs";
val (b2n_tm, mk_b2n, dest_b2n, is_b2n)  = syntax_fns1 "b2n";

val (bir_immtype_of_size_tm, mk_bir_immtype_of_size, dest_bir_immtype_of_size, is_bir_immtype_of_size)  = syntax_fns1 "bir_immtype_of_size";

val (type_of_bir_imm_tm, mk_type_of_bir_imm, dest_type_of_bir_imm, is_type_of_bir_imm)  = syntax_fns1 "type_of_bir_imm";

val (size_of_bir_immtype_tm, mk_size_of_bir_immtype, dest_size_of_bir_immtype, is_size_of_bir_immtype)  = syntax_fns1 "size_of_bir_immtype";



(* immediate sizes *)

val bir_immtype_t_sizes_list =
  map (fn tm => let
    val n = numSyntax.int_of_term (rhs (concl (EVAL (mk_size_of_bir_immtype tm))))
  in (n, tm)
  end) bir_immtype_t_list;

val known_imm_sizes = map fst bir_immtype_t_sizes_list;

fun bir_immtype_t_of_size n = assoc_with (op =) n bir_immtype_t_sizes_list handle HOL_ERR _ =>
  raise ERR "bir_immtype_t_of_size" "unknown size";

fun size_of_bir_immtype_t tm = rev_assoc_with (op ~~) tm bir_immtype_t_sizes_list handle HOL_ERR _ =>
  raise ERR "size_of_bir_immtype_t" "unknown value";

val bir_immtype_t_word_ty_list =
  map (fn (n, tm) => (wordsSyntax.mk_int_word_type n, tm)) bir_immtype_t_sizes_list;

fun bir_immtype_t_of_word_ty wty = assoc_with (op =) wty bir_immtype_t_word_ty_list handle HOL_ERR _ =>
  raise ERR "bir_immtype_t_of_word_ty" "unknown size";

fun word_ty_of_bir_immtype_t tm = rev_assoc_with (op ~~) tm bir_immtype_t_word_ty_list handle HOL_ERR _ =>
  raise ERR "word_ty_of_bir_immtype_t" "unknown value";

val is_known_word_ty = can bir_immtype_t_of_word_ty;
val is_known_imm_size = can bir_immtype_t_of_size;

val bir_immtype_t_imm_list =
  map (fn t => ((fst (dom_rng (type_of t))), t)) bir_imm_t_list;

fun gen_mk_Imm tm =
  if (wordsSyntax.is_word_type (type_of tm)) then
    (mk_comb (assoc_with (op =) (type_of tm) bir_immtype_t_imm_list, tm) handle HOL_ERR _ =>
     raise (ERR "gen_mkImm" ("unsupported word-type ``"^(type_to_string (type_of tm))^"``")))
  else if (type_of tm = bool) then
    mk_bool2b tm
  else if (type_of tm = listSyntax.mk_list_type bool) then let
    val l = length (fst (listSyntax.dest_list tm));
    val wty = fcpSyntax.mk_int_numeric_type l;
    val w = bitstringSyntax.mk_v2w (tm, wty)
  in
    gen_mk_Imm w
  end else
  raise (ERR "gen_mk_Imm" "unsupported type of argument");

val bir_imm_t_sizes_list =
  map (fn (wty, t) => (t,
    size_of_bir_immtype_t (bir_immtype_t_of_word_ty wty)))
    bir_immtype_t_imm_list;

local
  fun bir_imm_of_size_ n ((h:term * int)::t) =
	if n = (snd h)
	then (fst h)
	else if not (null t)
        then bir_imm_of_size_ n t
        else
	  raise (ERR "bir_imm_of_size"
		     ("The number of bits "^(Int.toString n)^
		      " does not correspond with any binary word"^
		      " length in supported BIR syntax."))
in
fun bir_imm_of_size n =
  bir_imm_of_size_ n bir_imm_t_sizes_list
end
;

fun gen_dest_Imm tm = let
  val (c, arg) = dest_comb tm;
  val s = assoc_with (op ~~) c bir_imm_t_sizes_list
in
  (s, arg)
end handle e => raise wrap_exn "gen_dest_Imm" e;

val gen_is_Imm = can gen_dest_Imm;

fun mk_Imm_of_num sz n =
  gen_mk_Imm (wordsSyntax.mk_wordi (n, sz));

fun mk_Imm_of_int sz n =
  gen_mk_Imm (wordsSyntax.mk_wordii (n, sz));


fun size_of_bir_immtype_t_dimindex_THM s = let
  val n = size_of_bir_immtype_t s
  val ty = fcpSyntax.mk_int_numeric_type n
  val tm = mk_eq (mk_size_of_bir_immtype s, wordsSyntax.mk_dimindex ty)
  val thm = simpLib.SIMP_PROVE (std_ss++wordsLib.WORD_ss) [size_of_bir_immtype_def] tm
in (ty, thm) end

fun MP_size_of_bir_immtype_t_EQ_dimindex thm = let
  fun mk_thm s = MATCH_MP thm (snd (size_of_bir_immtype_t_dimindex_THM s))
in
  map mk_thm bir_immtype_t_list
end;


fun build_immtype_t_conj_gen sv wty tt = let
  fun build_conj is = let
    val sty = wordsSyntax.dest_word_type (word_ty_of_bir_immtype_t is)
    val tt0 = inst [wty |-> sty] (subst [mk_var (sv, bir_immtype_t_ty) |-> is] tt)
  in
    tt0
  end

  val tt1 = list_mk_conj ((map build_conj bir_immtype_t_list))
in
  tt1
end;


fun build_immtype_t_conj tt = let
  val (v, tt0) = dest_forall tt
  val (vs, _) = dest_var v;
in
  build_immtype_t_conj_gen vs Type.alpha tt0
end;

end
