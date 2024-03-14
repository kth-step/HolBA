(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_expTheory;
open bir_envTheory;
open bir_valuesTheory;
open listTheory;

(* --------------------------------------------------------------------- *)
(* Symbolic Environment:                                                 *)
(* Same as Concrete Environment, with initially all                      *)
(* variables / flags set to symbols                                      *)
(* ----------------------------------------------------------------------*)

val _ = new_theory "bir_symb_env";

Datatype:
  bir_symb_var_environment_t = 
  BSEnv (string |-> (bir_type_t # (bir_exp_t)))
End
  

(* -----------------------------------------------------*)
(* Symbolic environment maps Vars to expressions        *)
(* ---------------------------------------------------- *)


Definition fmap_update_replace_def:
  fmap_update_replace (map: 'a |-> 'b) (a,  b) = 
    case (FLOOKUP map a) of 
    | NONE  => FUPDATE map (a, b)
    | SOME v => FUPDATE (map \\  a ) (a, b)
End

Definition bir_symb_env_read_def:
  (bir_symb_env_read v (BSEnv env) = 
        case (FLOOKUP  env (bir_var_name v)) of 
        | NONE => ARB (* this means we don't expect this case,
                         all variables of expressions should be in the environment *)
        | SOME (ty, e) => e)
End

Definition bir_symb_env_lookup_def:
  (bir_symb_env_lookup name (BSEnv env) = 
        FLOOKUP env name)
End

Definition bir_symb_env_update_def:
  bir_symb_env_update varname vo ty (BSEnv env) = 
    BSEnv (fmap_update_replace env (varname, (ty, vo)))
End

Definition bir_symb_env_lookup_type_def:
  bir_symb_env_lookup_type var (BSEnv env) = 
        case (FLOOKUP env (bir_var_name var)) of 
        | NONE => NONE 
        | SOME (ty, e) => SOME ty
End

Definition bir_symb_check_type_def:
  bir_symb_check_type var env =
        (bir_symb_env_lookup_type var env = SOME (bir_var_type var))
End

Definition bir_symb_varname_is_bound_def:
  bir_symb_varname_is_bound var_name (BSEnv env) = 
    case (FLOOKUP env var_name) of 
    | NONE => F 
    | SOME (_) => T
End

Definition bir_symb_env_write_def:
  bir_symb_env_write v exp env = 
    if bir_symb_check_type v env then 
      SOME (bir_symb_env_update (bir_var_name v) exp (bir_var_type v) env)
    else NONE
End

val _ = export_theory ();
