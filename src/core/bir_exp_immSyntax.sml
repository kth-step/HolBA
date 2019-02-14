structure bir_imm_expSyntax :> bir_imm_expSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_imm_expTheory
open bir_envTheory;

val ERR = mk_HOL_ERR "bir_imm_expSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_imm_exp";

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;


(* bir_unary_exp_t *)

val bir_unary_exp_t_ty = mk_type ("bir_unary_exp_t", []);

val (BIExp_ChangeSign_tm, is_BIExp_ChangeSign) = syntax_fns0 "BIExp_ChangeSign";
val (BIExp_Not_tm, is_BIExp_Not) = syntax_fns0 "BIExp_Not";
val (BIExp_CLZ_tm, is_BIExp_CLZ) = syntax_fns0 "BIExp_CLZ";
val (BIExp_CLS_tm, is_BIExp_CLS) = syntax_fns0 "BIExp_CLS";

val (bir_unary_exp_tm, mk_bir_unary_exp, dest_bir_unary_exp, is_bir_unary_exp) = syntax_fns2 "bir_unary_exp";


(* bin_bin_exp_t *)

val bir_bin_exp_t_ty = mk_type ("bir_bin_exp_t", []);

val (BIExp_And_tm, is_BIExp_And) = syntax_fns0 "BIExp_And";
val (BIExp_Or_tm, is_BIExp_Or) = syntax_fns0 "BIExp_Or";
val (BIExp_Xor_tm, is_BIExp_Xor) = syntax_fns0 "BIExp_Xor";
val (BIExp_Plus_tm, is_BIExp_Plus) = syntax_fns0 "BIExp_Plus";
val (BIExp_Minus_tm, is_BIExp_Minus) = syntax_fns0 "BIExp_Minus";
val (BIExp_Mult_tm, is_BIExp_Mult) = syntax_fns0 "BIExp_Mult";
val (BIExp_Div_tm, is_BIExp_Div) = syntax_fns0 "BIExp_Div";
val (BIExp_SignedDiv_tm, is_BIExp_SignedDiv) = syntax_fns0 "BIExp_SignedDiv";
val (BIExp_Mod_tm, is_BIExp_Mod) = syntax_fns0 "BIExp_Mod";
val (BIExp_SignedMod_tm, is_BIExp_SignedMod) = syntax_fns0 "BIExp_SignedMod";
val (BIExp_LeftShift_tm, is_BIExp_LeftShift) = syntax_fns0 "BIExp_LeftShift";
val (BIExp_RightShift_tm, is_BIExp_RightShift) = syntax_fns0 "BIExp_RightShift";
val (BIExp_SignedRightShift_tm, is_BIExp_SignedRightShift) = syntax_fns0 "BIExp_SignedRightShift";

val (bir_bin_exp_tm, mk_bir_bin_exp, dest_bir_bin_exp, is_bir_bin_exp) = syntax_fns3 "bir_bin_exp";


(* bin_bin_pred_t *)

val bir_bin_pred_t_ty = mk_type ("bir_bin_pred_t", []);

val (BIExp_Equal_tm, is_BIExp_Equal) = syntax_fns0 "BIExp_Equal";
val (BIExp_NotEqual_tm, is_BIExp_NotEqual) = syntax_fns0 "BIExp_NotEqual";
val (BIExp_LessThan_tm, is_BIExp_LessThan) = syntax_fns0 "BIExp_LessThan";
val (BIExp_SignedLessThan_tm, is_BIExp_SignedLessThan) = syntax_fns0 "BIExp_SignedLessThan";
val (BIExp_LessOrEqual_tm, is_BIExp_LessOrEqual) = syntax_fns0 "BIExp_LessOrEqual";
val (BIExp_SignedLessOrEqual_tm, is_BIExp_SignedLessOrEqual) = syntax_fns0 "BIExp_SignedLessOrEqual";

val (bir_bin_pred_tm, mk_bir_bin_pred, dest_bir_bin_pred, is_bir_bin_pred) = syntax_fns3 "bir_bin_pred";



(* Casts *)

val bir_cast_t_ty = mk_type ("bir_cast_t", []);

val (BIExp_UnsignedCast_tm, is_BIExp_UnsignedCast) = syntax_fns0 "BIExp_UnsignedCast";
val (BIExp_SignedCast_tm, is_BIExp_SignedCast) = syntax_fns0 "BIExp_SignedCast";
val (BIExp_HighCast_tm, is_BIExp_HighCast) = syntax_fns0 "BIExp_HighCast";
val (BIExp_LowCast_tm, is_BIExp_LowCast) = syntax_fns0 "BIExp_LowCast";

val (bir_gencast_tm, mk_bir_gencast, dest_bir_gencast, is_bir_gencast) = syntax_fns3 "bir_gencast";


end
