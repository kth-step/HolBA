signature bir_envSyntax =
sig
   include Abbrev


   (*************************)
   (* bir_var_environment_t *)
   (*************************)

   val bir_var_environment_t_ty : hol_type;

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

   val bir_env_write_tm      : term;
   val mk_bir_env_write      : term * term * term -> term;
   val dest_bir_env_write    : term -> term * term * term;
   val is_bir_env_write      : term -> bool;

   val bir_env_read_tm      : term;
   val mk_bir_env_read      : term * term -> term;
   val dest_bir_env_read    : term -> term * term;
   val is_bir_env_read      : term -> bool;

   val bir_env_var_is_well_typed_tm   : term;
   val mk_bir_env_var_is_well_typed   : term * term -> term;
   val dest_bir_env_var_is_well_typed : term -> term * term;
   val is_bir_env_var_is_well_typed   : term -> bool;

   val bir_env_order_tm   : term;
   val mk_bir_env_order   : term * term -> term;
   val dest_bir_env_order : term -> term * term;
   val is_bir_env_order   : term -> bool;

end
