structure bir_wm_instSyntax :> bir_wm_instSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_wm_instTheory;


val ERR = mk_HOL_ERR "bir_wm_instSyntax"
val wrap_exn = Feedback.wrap_exn "bir_wm_instSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_wm_inst"

fun dest_septop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7) else raise e
    | _ => raise e
fun list_of_septuple (a, b, c, d, e, f, g) = [a, b, c, d, e, f, g];
fun mk_septop tm = HolKernel.list_mk_icomb tm o list_of_septuple

val syntax_fns7 = syntax_fns 7 dest_septop mk_septop;

(* bir_map_triple *)
val (bir_map_triple_tm, mk_bir_map_triple, dest_bir_map_triple, is_bir_map_triple) = syntax_fns7 "bir_map_triple";

end
