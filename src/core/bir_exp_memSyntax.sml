structure bir_mem_expSyntax :> bir_mem_expSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_mem_expTheory;
open bir_immSyntax;

val ERR = mk_HOL_ERR "bir_mem_expSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_mem_exp";

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;


(* Endian *)

val bir_endian_t_ty = mk_type ("bir_endian_t", []);
val (BEnd_BigEndian_tm,    is_BEnd_BigEndian)    = syntax_fns0 "BEnd_BigEndian";
val (BEnd_LittleEndian_tm, is_BEnd_LittleEndian) = syntax_fns0 "BEnd_LittleEndian";
val (BEnd_NoEndian_tm,     is_BEnd_NoEndian)     = syntax_fns0 "BEnd_NoEndian";

end
