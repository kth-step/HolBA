structure bilSimps :> bilSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bilTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;
open bil_imm_expTheory bil_mem_expTheory bil_envTheory;
open bil_expTheory bil_programTheory bil_typingTheory;

val bil_list_of_types = [
   mk_thy_type {Tyop="bil_imm_t",            Thy="bil_imm", Args=[]},
   mk_thy_type {Tyop="bil_immtype_t",        Thy="bil_imm", Args=[]},

   mk_thy_type {Tyop="bil_unary_exp_t",      Thy="bil_imm_exp", Args=[]},
   mk_thy_type {Tyop="bil_bin_exp_t",        Thy="bil_imm_exp", Args=[]},
   mk_thy_type {Tyop="bil_bin_pred_t",       Thy="bil_imm_exp", Args=[]},
   mk_thy_type {Tyop="bil_cast_t",           Thy="bil_imm_exp", Args=[]},

   mk_thy_type {Tyop="bil_endian_t",         Thy="bil_mem_exp", Args=[]},

   mk_thy_type {Tyop="bil_val_t",            Thy="bil_values", Args=[]},
   mk_thy_type {Tyop="bil_type_t",           Thy="bil_values", Args=[]},

   mk_thy_type {Tyop="bil_var_t",            Thy="bil_env", Args=[]},
   mk_thy_type {Tyop="bil_var_environment_t",Thy="bil_env", Args=[]},
   mk_thy_type {Tyop="bil_env_cond_t",       Thy="bil_env", Args=[]},

   mk_thy_type {Tyop="bil_label_t",          Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_stmt_t",           Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_block_t",          Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_program_t",        Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_programcounter_t", Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_termcode_t",       Thy="bil_program", Args=[]},
   mk_thy_type {Tyop="bil_state_t",          Thy="bil_program", Args=[]}
];



val bil_TYPES_ss = rewrites (flatten (map type_rws bil_list_of_types))

val bil_SIMPLE_REWRS_imm = rewrites [
  type_of_bil_imm_def,
  type_of_n2bs,
  type_of_n2b_fixed,
  type_of_w2bs,
  type_of_bool2b,
  type_of_v2bs,
  w2bs_REWRS,
  v2bs_REWRS,
  b2v_def,
  v2n_b2v,

  n2bs_b2n,
  b2n_def,
  n2bs_def,
  b2w_REWRS,
  w2bs_REWRS,
  w2bs_b2w,
  v2n_w2v,
  bool2b_inv,
  wordsTheory.n2w_w2n,

  size_of_bil_immtype_INJ,
  size_of_bil_immtype_NEQ_0,
  is_valid_bil_immtype_size_IMP,
  bil_immtype_of_num_inv 
];


val bil_SIMPLE_REWRS_env = rewrites [
  bil_var_name_def,
  bil_var_type_def,
  is_env_regular_def,
  is_valid_env_empty,
  bil_env_write_Irregular,
  bil_env_write_Irregular_WrongVal
]




val bil_SIMPLE_REWRS_imm_exp = rewrites [
  bil_unary_exp_GET_OPER_def,
  bil_bin_exp_GET_OPER_def,
  bil_bin_pred_GET_OPER_def,
  bil_gencast_def,
  bil_unary_exp_REWRS,
  bil_bin_exp_REWRS,

  type_of_bil_unary_exp,
  type_of_bil_unary_exps,
  bil_unary_exps_REWRS,
  type_of_bil_bin_exp,
  type_of_bil_bin_exps,
  bil_bin_exps_REWRS,
  bil_bin_pred_REWRS,
  bil_bin_preds_REWRS,

  bil_cast_REWRS,
  bil_lcast_def,
  bil_hcast_REWRS,
  bil_scast_REWRS,

  type_of_bil_gencast,
  bil_gencast_ID,
  bil_casts_ID,
  bil_casts_Bit1,
  type_of_bil_casts
];


val bil_SIMPLE_REWRS_mem_exp = rewrites [
  bil_number_of_mem_splits_REWRS,
  bil_number_of_mem_splits_NEQ_SOME0,
  bil_number_of_mem_splits_ID,
  bil_number_of_mem_splits_EQ_SOME1,

  type_of_bil_mem_concat,
  type_of_bil_load_from_mem,
  bil_load_from_mem_NONE_REWRS,
  bil_load_from_mem_EQ_NONE_IMP,

  bil_load_from_mem_used_addrs_REWRS,
  bil_load_from_mem_used_addrs_FINITE,
  bil_load_from_mem_used_addrs_EMPTY,

  bil_store_in_mem_NONE_REWRS,
  bil_store_in_mem_EQ_NONE_IMP,
  bil_store_in_mem_used_addrs_REWRS,
  bil_store_in_mem_used_addrs_FINITE,
  bil_store_in_mem_used_addrs_EMPTY
];
  


val bil_SIMPLE_REWRS_mem_exp = rewrites [
  bil_number_of_mem_splits_REWRS,
  bil_number_of_mem_splits_NEQ_SOME0,
  bil_number_of_mem_splits_ID,
  bil_number_of_mem_splits_EQ_SOME1,

  type_of_bil_mem_concat,
  type_of_bil_load_from_mem,
  bil_load_from_mem_NONE_REWRS,
  bil_load_from_mem_EQ_NONE_IMP,

  bil_load_from_mem_used_addrs_REWRS,
  bil_load_from_mem_used_addrs_FINITE,
  bil_load_from_mem_used_addrs_EMPTY,

  bil_store_in_mem_NONE_REWRS,
  bil_store_in_mem_EQ_NONE_IMP,
  bil_store_in_mem_used_addrs_REWRS,
  bil_store_in_mem_used_addrs_FINITE,
  bil_store_in_mem_used_addrs_EMPTY
];
  

val bil_SIMPLE_REWRS_values = rewrites [
  bil_val_checker_REWRS,
  type_of_bil_val_def,
  bil_type_checker_REWRS,
  bil_type_is_BoolType_IMPL
];

val bil_SIMPLE_REWRS_exp = rewrites [
  bil_eval_exp_def,
  bil_eval_cast_REWRS,
  bil_eval_unary_exp_REWRS,
  bil_eval_bin_exp_REWRS,
  bil_eval_bin_pred_REWRS,
  bil_eval_ifthenelse_REWRS,
  bil_eval_ifthenelse_REWRS_Unknown,
  bil_eval_load_Unknown_REWRS,
  bil_eval_store_Unknown_REWRS
];

val bil_SIMPLE_REWRS_program = rewrites [
  bil_stmt_to_string_def,
  r2s_REWRS,
  bil_state_is_terminated_IMP,
  bil_declare_initial_value_def
];

val bil_SIMPLE_REWRS_typing = rewrites [
  type_of_bil_exp_EQ_SOME_REWRS,
  type_of_bil_exp_EQ_NONE_REWRS
];

val bil_SIMPLE_REWRS_ss = simpLib.merge_ss [
  bil_TYPES_ss,
  bil_SIMPLE_REWRS_imm,
  bil_SIMPLE_REWRS_values,
  bil_SIMPLE_REWRS_env,
  bil_SIMPLE_REWRS_imm_exp,
  bil_SIMPLE_REWRS_mem_exp,
  bil_SIMPLE_REWRS_exp,
  bil_SIMPLE_REWRS_program,
  bil_SIMPLE_REWRS_typing
];

val bil_ss = bil_SIMPLE_REWRS_ss;

end
