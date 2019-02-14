structure bir_interval_expSyntax :> bir_interval_expSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_interval_expTheory wordsSyntax


val ERR = mk_HOL_ERR "bir_interval_expSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_interval_exp"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;


(* bir_word_interval_t *)

fun mk_word_interval_t_ty ty = mk_type ("word_interval_t", [ty]);

fun dest_word_interval_t_ty ty =
   case total dest_thy_type ty
    of SOME {Tyop="word_interval_t", Thy="bir_interval_exp", Args=[ty]} => ty
     | other => raise ERR "dest_word_interval_t_ty" ""

val is_word_interval_t_ty = can dest_word_interval_t_ty;

(* Common functions *)

val (WI_end_tm,  mk_WI_end, dest_WI_end, is_WI_end)  = syntax_fns2 "WI_end";
val (WI_size_tm,  mk_WI_size, dest_WI_size, is_WI_size)  = syntax_fns2 "WI_size";

val (WI_wf_tm,  mk_WI_wf, dest_WI_wf, is_WI_wf)  = syntax_fns1 "WI_wf";
val (WI_wfe_tm,  mk_WI_wfe, dest_WI_wfe, is_WI_wfe)  = syntax_fns1 "WI_wfe";
val (WI_MEM_tm,  mk_WI_MEM, dest_WI_MEM, is_WI_MEM)  = syntax_fns2 "WI_MEM";
val (WI_ELEM_LIST_tm,  mk_WI_ELEM_LIST, dest_WI_ELEM_LIST, is_WI_ELEM_LIST)  = syntax_fns2 "WI_ELEM_LIST";
val (WI_is_empty_tm,  mk_WI_is_empty, dest_WI_is_empty, is_WI_is_empty)  = syntax_fns1 "WI_is_empty";
val (WI_is_sub_tm,  mk_WI_is_sub, dest_WI_is_sub, is_WI_is_sub)  = syntax_fns2 "WI_is_sub";
val (WI_overlap_tm,  mk_WI_overlap, dest_WI_overlap, is_WI_overlap)  = syntax_fns2 "WI_overlap";
val (WI_distinct_tm,  mk_WI_distinct, dest_WI_distinct, is_WI_distinct)  = syntax_fns2 "WI_distinct";
val (FUNS_EQ_OUTSIDE_WI_size_tm,  mk_FUNS_EQ_OUTSIDE_WI_size, dest_FUNS_EQ_OUTSIDE_WI_size, is_FUNS_EQ_OUTSIDE_WI_size)  = syntax_fns4 "FUNS_EQ_OUTSIDE_WI_size";

(* Fancy constructors *)

(* Debug

   val b_n = Arbnum.fromInt 10;
   val e_n = Arbnum.fromInt 20;
   val sz_n = Arbnum.fromInt 10;
   val wty = ``:32``
*)

fun mk_WI_end_of_nums wty b_n e_n = let
  val b_t = wordsSyntax.mk_n2w (numSyntax.mk_numeral b_n, wty);
  val e_t = wordsSyntax.mk_n2w (numSyntax.mk_numeral e_n, wty);
in
  mk_WI_end (b_t, e_t)
end;

fun mk_WI_size_of_nums wty b_n sz_n = let
  val b_t = wordsSyntax.mk_n2w (numSyntax.mk_numeral b_n, wty);
  val sz_t = wordsSyntax.mk_n2w (numSyntax.mk_numeral sz_n, wty);
in
  mk_WI_size (b_t, sz_t)
end;

fun mk_WI_end_of_nums_WFE wty b_n e_n = let
  val i_t = mk_WI_end_of_nums wty b_n e_n
  val thm_t = mk_WI_wfe i_t
  val thm = prove (``^thm_t``, SIMP_TAC (arith_ss++wordsLib.WORD_ss) [WI_wfe_End])
in
  (i_t, thm)
end;

fun mk_WI_size_of_nums_WFE wty b_n sz_n = let
  val i_t = mk_WI_size_of_nums wty b_n sz_n
  val thm_t = mk_WI_wfe i_t
  val thm = prove (``^thm_t``, SIMP_TAC (arith_ss++wordsLib.WORD_ss) [WI_wfe_Size])
in
  (i_t, thm)
end;


end
