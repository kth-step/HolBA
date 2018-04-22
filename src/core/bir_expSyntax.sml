structure bir_expSyntax :> bir_expSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open bir_valuesSyntax bir_immSyntax;

val ERR = mk_HOL_ERR "bir_expSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;


(*************)
(* bir_exp_t *)
(*************)

val bir_exp_t_ty = mk_type ("bir_exp_t", []);

val (BExp_Const_tm, mk_BExp_Const, dest_BExp_Const, is_BExp_Const) = syntax_fns1 "BExp_Const";
val (BExp_Den_tm, mk_BExp_Den, dest_BExp_Den, is_BExp_Den) = syntax_fns1 "BExp_Den";
val (BExp_Cast_tm, mk_BExp_Cast, dest_BExp_Cast, is_BExp_Cast) = syntax_fns3 "BExp_Cast";
val (BExp_UnaryExp_tm, mk_BExp_UnaryExp, dest_BExp_UnaryExp, is_BExp_UnaryExp) = syntax_fns2 "BExp_UnaryExp";
val (BExp_BinExp_tm, mk_BExp_BinExp, dest_BExp_BinExp, is_BExp_BinExp) = syntax_fns3 "BExp_BinExp";
val (BExp_BinPred_tm, mk_BExp_BinPred, dest_BExp_BinPred, is_BExp_BinPred) = syntax_fns3 "BExp_BinPred";
val (BExp_MemEq_tm, mk_BExp_MemEq, dest_BExp_MemEq, is_BExp_MemEq) = syntax_fns2 "BExp_MemEq";
val (BExp_IfThenElse_tm, mk_BExp_IfThenElse, dest_BExp_IfThenElse, is_BExp_IfThenElse) = syntax_fns3 "BExp_IfThenElse";
val (BExp_Load_tm, mk_BExp_Load, dest_BExp_Load, is_BExp_Load) = syntax_fns4 "BExp_Load";
val (BExp_Store_tm, mk_BExp_Store, dest_BExp_Store, is_BExp_Store) = syntax_fns4 "BExp_Store";


end
