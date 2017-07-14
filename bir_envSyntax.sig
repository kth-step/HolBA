signature bir_envSyntax =
sig
   include Abbrev


   (*************************)
   (* bir_var_environment_t *)
   (*************************)

   val bir_var_environment_t_ty : hol_type;

   val bir_empty_env_tm : term;
   val is_bir_empty_env : term -> bool;

   val BEnv_tm   : term;
   val mk_BEnv   : term -> term;
   val dest_BEnv : term -> term;
   val is_BEnv   : term -> bool;


   (*************)
   (* variables *)
   (*************)

   val bir_var_t_ty     : hol_type

   val BVar_tm          : term
   val dest_BVar        : term -> term * term
   val dest_BVar_string : term -> string * term
   val is_BVar          : term -> bool
   val mk_BVar          : term * term -> term
   val mk_BVar_string   : string * term -> term


   val bir_var_name_tm   : term;
   val mk_bir_var_name   : term -> term;
   val dest_bir_var_name : term -> term;
   val is_bir_var_name   : term -> bool;

   val bir_var_type_tm   : term;
   val mk_bir_var_type   : term -> term;
   val dest_bir_var_type : term -> term;
   val is_bir_var_type   : term -> bool;


   (*************)
   (* Misc      *)
   (*************)

   val bir_is_well_typed_env_tm   : term;
   val mk_bir_is_well_typed_env   : term -> term;
   val dest_bir_is_well_typed_env : term -> term;
   val is_bir_is_well_typed_env   : term -> bool;

   val bir_env_varname_is_bound_tm          : term;
   val mk_bir_env_varname_is_bound          : term * term -> term;
   val mk_bir_env_varname_is_bound_string   : string * term -> term;
   val dest_bir_env_varname_is_bound        : term -> term * term;
   val dest_bir_env_varname_is_bound_string : term -> string * term;
   val is_bir_env_varname_is_bound          : term -> bool;

   val bir_env_var_is_initialised_tm   : term;
   val mk_bir_env_var_is_initialised   : term * term -> term;
   val dest_bir_env_var_is_initialised : term -> term * term;
   val is_bir_env_var_is_initialised   : term -> bool;

   val bir_env_var_is_declared_tm   : term;
   val mk_bir_env_var_is_declared   : term * term -> term;
   val dest_bir_env_var_is_declared : term -> term * term;
   val is_bir_env_var_is_declared   : term -> bool;

   val bir_env_order_tm   : term;
   val mk_bir_env_order   : term * term -> term;
   val dest_bir_env_order : term -> term * term;
   val is_bir_env_order   : term -> bool;

end
