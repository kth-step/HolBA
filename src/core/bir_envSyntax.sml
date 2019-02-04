structure bir_envSyntax :> bir_envSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory;
open bir_envTheory;
open bir_valuesSyntax bir_immSyntax;

val ERR = mk_HOL_ERR "bir_envSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_env";

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;


(* Environments *)

val bir_var_environment_t_ty = mk_type ("bir_var_environment_t", []);
val (bir_empty_env_tm, is_bir_empty_env) = syntax_fns0 "bir_empty_env";
val (BEnv_tm, mk_BEnv, dest_BEnv, is_BEnv) = syntax_fns1 "BEnv";




(* Vars *)

val bir_var_t_ty = mk_type ("bir_var_t", []);
val (BVar_tm, mk_BVar, dest_BVar, is_BVar)  = syntax_fns2 "BVar";

fun mk_BVar_string (s, ty) = mk_BVar (stringSyntax.fromMLstring s, ty);
fun dest_BVar_string tm = let
  val (ntm, ty_tm) = dest_BVar tm
in
  (stringSyntax.fromHOLstring ntm, ty_tm)
end;


val (bir_var_name_tm, mk_bir_var_name, dest_bir_var_name, is_bir_var_name) = syntax_fns1 "bir_var_name";

val (bir_var_type_tm, mk_bir_var_type, dest_bir_var_type, is_bir_var_type) = syntax_fns1 "bir_var_type";


(* Misc *)

val (bir_env_write_tm, mk_bir_env_write, dest_bir_env_write, is_bir_env_write) = syntax_fns3 "bir_env_write";

val (bir_is_well_typed_env_tm, mk_bir_is_well_typed_env, dest_bir_is_well_typed_env, is_bir_is_well_typed_env) = syntax_fns1 "bir_is_well_typed_env";

val (bir_env_varname_is_bound_tm, mk_bir_env_varname_is_bound, dest_bir_env_varname_is_bound, is_bir_env_varname_is_bound) = syntax_fns2 "bir_env_varname_is_bound";

fun mk_bir_env_varname_is_bound_string (s, tm) = mk_bir_env_varname_is_bound (stringSyntax.fromMLstring s, tm);

fun dest_bir_env_varname_is_bound_string tm = let
  val (s, t) = dest_bir_env_varname_is_bound tm
in
  (stringSyntax.fromHOLstring s, t)
end;


val (bir_env_var_is_initialised_tm, mk_bir_env_var_is_initialised, dest_bir_env_var_is_initialised, is_bir_env_var_is_initialised) = syntax_fns2 "bir_env_var_is_initialised";

val (bir_env_var_is_declared_tm, mk_bir_env_var_is_declared, dest_bir_env_var_is_declared, is_bir_env_var_is_declared) = syntax_fns2 "bir_env_var_is_declared";

val (bir_env_order_tm, mk_bir_env_order, dest_bir_env_order, is_bir_env_order) = syntax_fns2 "bir_env_order";

end
