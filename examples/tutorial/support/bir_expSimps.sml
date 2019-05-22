structure bir_expSimps :> bir_expSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory
     bir_exp_immTheory bir_exp_memTheory bir_envTheory
     bir_expTheory bir_programTheory bir_typing_progTheory
     bir_typing_expTheory;

open bir_bool_expTheory;

val bir_list_of_types = [
   mk_thy_type {Tyop="bir_immtype_t", Thy="bir_imm", Args=[]},
   mk_thy_type {Tyop="bir_endian_t",  Thy="bir_exp_mem", Args=[]},
   mk_thy_type {Tyop="bir_type_t",    Thy="bir_values", Args=[]}
];

val type_thms = rewrites (flatten (map type_rws bir_list_of_types));

val thms = rewrites [
(* Theorems needed from outside holBACore_ss: *)
  bir_is_bool_exp_def,
  BType_Bool_def,
(* Theorems from constituents of bir_SIMPLE_REWRS_ss: *)
  type_of_bir_imm_def,

  bir_var_type_def,

  bir_number_of_mem_splits_REWRS,
  bir_store_in_mem_NONE_REWRS,

  bir_type_checker_REWRS,
  bir_type_is_Bool_IMPL,

  type_of_bir_exp_EQ_SOME_REWRS,
  bir_vars_of_exp_def
];

val bir_is_bool_ss = simpLib.merge_ss [type_thms, thms];

(* Useful when simplifying bir_env_read. *)
val bir_type_val_opt_ss =
  DatatypeSimps.case_cong_ss [``:bir_type_t # bir_val_t option``];

end
