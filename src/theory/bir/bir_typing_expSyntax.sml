structure bir_typing_expSyntax :> bir_typing_expSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_typing_expTheory;


val ERR = mk_HOL_ERR "bir_typing_expSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_typing_exp"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;

val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;


(* constants*)

val (bir_exp_is_well_typed_tm,  mk_bir_exp_is_well_typed, dest_bir_exp_is_well_typed, is_bir_exp_is_well_typed)  = syntax_fns1 "bir_exp_is_well_typed";

val (bir_vars_of_exp_tm,  mk_bir_vars_of_exp, dest_bir_vars_of_exp, is_bir_vars_of_exp)  = syntax_fns1_set "bir_vars_of_exp";

val (type_of_bir_exp_tm,  mk_type_of_bir_exp, dest_type_of_bir_exp, is_type_of_bir_exp)  = syntax_fns1 "type_of_bir_exp";

end
