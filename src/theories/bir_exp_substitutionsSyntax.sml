structure bir_exp_substitutionsSyntax :> bir_exp_substitutionsSyntax =
struct

open HolKernel Parse boolLib bossLib


val ERR = mk_HOL_ERR "bir_exp_substitutionsSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp_substitutions"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;

(* *)

val (bir_exp_subst1_tm, mk_bir_exp_subst1, dest_bir_exp_subst1, is_bir_exp_subst1) = syntax_fns3 "bir_exp_subst1";

end
