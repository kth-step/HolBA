(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_envTheory;
open bir_valuesTheory;
open listTheory;

(* --------------------------------------------------------------------- *)
(* Symbolic Environment:                                                 *)
(* Same as Concrete Environment, with initially all                      *)
(* variables / flags set to symbols                                      *)
(* ----------------------------------------------------------------------*)

val _ = new_theory "bir_symb2_env";

val _ = Datatype `bir_symb_var_environment_t = 
  BEnv (string |-> (bir_type_t # (bir_exp_t)))`;
  

(* -----------------------------------------------------*)
(* Symbolic environment maps Vars to expressions        *)
(* ---------------------------------------------------- *)


val fmap_update_replace_def = Define `
    fmap_update_replace (map: 'a |-> 'b) (a,  b) = 
    case (FLOOKUP map a) of 
    | NONE  => FUPDATE map (a, b)
    | SOME v => FUPDATE (map \\  a ) (a, b)`;

val bir_symb_env_read_def  = Define `
    (bir_symb_env_read v (BEnv env) = 
        case (FLOOKUP  env (bir_var_name v)) of 
        | NONE => ARB (* this means we don't expect this case,
                         all variables of expressions should be in the environment *)
        | SOME (ty, e) => e)`;

val bir_symb_env_lookup_def = Define `
    (bir_symb_env_lookup name (BEnv env) = 
        FLOOKUP env name)`;

val bir_symb_env_update_def = Define `
    bir_symb_env_update varname vo ty (BEnv env) = 
    BEnv (fmap_update_replace env (varname, (ty, vo)))`;

val bir_symb_env_lookup_type_def = Define `
    bir_symb_env_lookup_type var (BEnv env) = 
        case (FLOOKUP env (bir_var_name var)) of 
        | NONE => NONE 
        | SOME (ty, e) => SOME ty`;

val bir_symb_check_type_def = Define `  
    bir_symb_check_type var env =
        (bir_symb_env_lookup_type var env = SOME (bir_var_type var))`;

val bir_symb_varname_is_bound_def = Define `
    bir_symb_varname_is_bound var_name (BEnv env) = 
    case (FLOOKUP env var_name) of 
    | NONE => F 
    | SOME (_) => T`;

val bir_symb_env_write_def = Define `
    bir_symb_env_write v exp env = 
    if bir_symb_check_type v env then 
      SOME (bir_symb_env_update (bir_var_name v) exp (bir_var_type v) env)
    else NONE`;

val _ = export_theory ();
