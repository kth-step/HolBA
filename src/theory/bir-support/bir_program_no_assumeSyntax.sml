structure bir_program_no_assumeSyntax :> bir_program_no_assumeSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_program_no_assumeTheory;


val ERR = mk_HOL_ERR "bir_program_no_assumeSyntax"
val wrap_exn = Feedback.wrap_exn "bir_program_no_assumeSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_no_assume"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;

val (bir_prog_has_no_assumes_tm, mk_bir_prog_has_no_assumes, dest_bir_prog_has_no_assumes, is_bir_prog_has_no_assumes) = syntax_fns1 "bir_prog_has_no_assumes";
val (bir_block_has_no_assumes_tm, mk_bir_block_has_no_assumes, dest_bir_block_has_no_assumes, is_bir_block_has_no_assumes) = syntax_fns1 "bir_block_has_no_assumes";
val (bir_stmtsB_has_no_assumes_tm, mk_bir_stmtsB_has_no_assumes, dest_bir_stmtsB_has_no_assumes, is_bir_stmtsB_has_no_assumes) = syntax_fns1 "bir_stmtsB_has_no_assumes";
val (bir_stmtB_is_not_assume_tm, mk_bir_stmtB_is_not_assume, dest_bir_stmtB_is_not_assume, is_bir_stmtB_is_not_assume) = syntax_fns1 "bir_stmtB_is_not_assume";

end
