structure bir_program_labelsSyntax :> bir_program_labelsSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_program_labelsTheory;


val ERR = mk_HOL_ERR "bir_program_labelsSyntax"
val wrap_exn = Feedback.wrap_exn "bir_program_labelsSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_labels"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;

val (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC)  = syntax_fns2 "BL_Address_HC";

end
