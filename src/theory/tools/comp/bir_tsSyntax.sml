structure bir_tsSyntax :> bir_tsSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_tsTheory;


val ERR = mk_HOL_ERR "bir_tsSyntax"
val wrap_exn = Feedback.wrap_exn "bir_tsSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_ts"

fun dest_septop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7) else raise e
    | _ => raise e
fun list_of_septuple (a, b, c, d, e, f, g) = [a, b, c, d, e, f, g];
fun mk_septop tm = HolKernel.list_mk_icomb tm o list_of_septuple

val syntax_fns7 = syntax_fns 7 dest_septop mk_septop;

(* bir_cont *)
val (bir_cont_tm, mk_bir_cont, dest_bir_cont, is_bir_cont) = syntax_fns7 "bir_cont";

end
