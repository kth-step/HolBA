structure bir_typing_progSyntax :> bir_typing_progSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_typing_progTheory;


val ERR = mk_HOL_ERR "bir_typing_progSyntax"
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_typing_prog"

val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;


(* constants*)

val (bir_vars_of_program_tm,  mk_bir_vars_of_program, dest_bir_vars_of_program, is_bir_vars_of_program)  = syntax_fns1_set "bir_vars_of_program";

end
