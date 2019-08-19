structure bir_htSyntax :> bir_htSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_htTheory;


val ERR = mk_HOL_ERR "bir_htSyntax"
val wrap_exn = Feedback.wrap_exn "bir_htSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_ht"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e
fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;
val syntax_fns5 = syntax_fns 5 dest_quinop mk_quinop;

(* bir_exec_to_labels_triple *)
val (bir_exec_to_labels_triple_tm, mk_bir_exec_to_labels_triple, dest_bir_exec_to_labels_triple, is_bir_exec_to_labels_triple) = syntax_fns5 "bir_exec_to_labels_triple";

end
