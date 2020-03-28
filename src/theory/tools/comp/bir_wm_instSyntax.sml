structure bir_wm_instSyntax :> bir_wm_instSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_wm_instTheory;


val ERR = mk_HOL_ERR "bir_wm_instSyntax"
val wrap_exn = Feedback.wrap_exn "bir_wm_instSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_wm_inst"

fun dest_sextop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6) else raise e
    | _ => raise e
fun list_of_sextuple (a, b, c, d, e, f) = [a, b, c, d, e, f];
fun mk_sextop tm = HolKernel.list_mk_icomb tm o list_of_sextuple

val syntax_fns6 = syntax_fns 6 dest_sextop mk_sextop;

(* bir_map_triple *)
val (bir_map_triple_tm, mk_bir_map_triple, dest_bir_map_triple, is_bir_map_triple) = syntax_fns6 "bir_map_triple";

end
