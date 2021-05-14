structure bir_exp_liftingSyntax :> bir_exp_liftingSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_exp_liftingTheory;

val ERR = mk_HOL_ERR "bir_exp_liftingSyntax"

val syntax_fns1 = syntax_fns1 "bir_exp_lifting";
val syntax_fns3 = syntax_fns3 "bir_exp_lifting";


fun mk_bir_lift_val_t (ty1, ty2) =
   Type.mk_thy_type {Tyop = "bir_lift_val_t", Thy = "bir_exp_lifting", Args = [ty1, ty2]};

fun dest_bir_lift_val_t ty =
   case total dest_thy_type ty of
      SOME{Tyop = "bir_lift_val_t", Thy = "bir_exp_lifting", Args = [ty1, ty2]} => (ty1, ty2)
    | other => raise ERR "dest_bir_lift_val_t" "Invalid argument.";

val is_bir_lift_val_t = can dest_bir_lift_val_t;


val (bir_is_lifted_exp_tm, mk_bir_is_lifted_exp, dest_bir_is_lifted_exp, is_bir_is_lifted_exp)  = syntax_fns3 "bir_is_lifted_exp";


val (BLV_Imm_tm, mk_BLV_Imm, dest_BLV_Imm, is_BLV_Imm) = syntax_fns1 "BLV_Imm";
val (BLV_Mem_tm, mk_BLV_Mem, dest_BLV_Mem, is_BLV_Mem) = syntax_fns1 "BLV_Mem";

fun gen_mk_BLV t =
  mk_BLV_Imm (bir_immSyntax.gen_mk_Imm t) handle HOL_ERR _ =>
  mk_BLV_Mem t handle HOL_ERR _ =>
  mk_BLV_Imm t handle HOL_ERR _ =>
  raise (ERR "gen_mk_BLV" "");

end
