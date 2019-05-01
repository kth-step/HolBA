structure HolBACoreSimps :> HolBACoreSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_expTheory bir_programTheory bir_typing_progTheory;
open bir_typing_expTheory;

val bir_list_of_types = [
   mk_thy_type {Tyop="bir_imm_t",            Thy="bir_imm", Args=[]},
   mk_thy_type {Tyop="bir_immtype_t",        Thy="bir_imm", Args=[]},

   mk_thy_type {Tyop="bir_unary_exp_t",      Thy="bir_exp_imm", Args=[]},
   mk_thy_type {Tyop="bir_bin_exp_t",        Thy="bir_exp_imm", Args=[]},
   mk_thy_type {Tyop="bir_bin_pred_t",       Thy="bir_exp_imm", Args=[]},
   mk_thy_type {Tyop="bir_cast_t",           Thy="bir_exp_imm", Args=[]},

   mk_thy_type {Tyop="bir_endian_t",         Thy="bir_exp_mem", Args=[]},

   mk_thy_type {Tyop="bir_val_t",            Thy="bir_values", Args=[]},
   mk_thy_type {Tyop="bir_type_t",           Thy="bir_values", Args=[]},

   mk_thy_type {Tyop="bir_var_t",            Thy="bir_env", Args=[]},
   mk_thy_type {Tyop="bir_var_environment_t",Thy="bir_env", Args=[]},
   mk_thy_type {Tyop="bir_env_cond_t",       Thy="bir_env", Args=[]},

   mk_thy_type {Tyop="bir_label_t",          Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_label_exp_t",      Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_stmt_end_t",       Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_stmt_basic_t",     Thy="bir_program", Args=[Type.alpha]},
   mk_thy_type {Tyop="bir_stmt_t",           Thy="bir_program", Args=[Type.alpha]},
   mk_thy_type {Tyop="bir_block_t",          Thy="bir_program", Args=[Type.alpha]},
   mk_thy_type {Tyop="bir_program_t",        Thy="bir_program", Args=[Type.alpha]},
   mk_thy_type {Tyop="bir_programcounter_t", Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_status_t",         Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_state_t",          Thy="bir_program", Args=[]},
   mk_thy_type {Tyop="bir_execution_result_t", Thy="bir_program", Args=[Type.alpha]}
];


val bir_TYPES_ss = rewrites (flatten (map type_rws bir_list_of_types))

val bir_SIMPLE_REWRS_imm = rewrites [
  type_of_bir_imm_def,
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
  bool2b_EQ_IMM1_ELIMS,
  bool2b_NEQ_IMM_ELIMS,
  bool2b_11,
  wordsTheory.n2w_w2n,

  size_of_bir_immtype_INJ,
  size_of_bir_immtype_NEQ_0,
  is_valid_bir_immtype_size_IMP,
  bir_immtype_of_num_inv,
  size_of_bir_immtype_def
];


val bir_SIMPLE_REWRS_env = rewrites [
  bir_var_name_def,
  bir_var_type_def,
  bir_is_well_typed_env_empty,
  bir_env_write_WrongVal
];



val bir_SIMPLE_REWRS_imm_exp = rewrites [
  bir_unary_exp_GET_OPER_def,
  bir_bin_exp_GET_OPER_def,
  bir_bin_pred_GET_OPER_def,
  bir_gencast_def,
  bir_unary_exp_REWRS,
  bir_bin_exp_REWRS,
  bir_bin_pred_REWRS,

  type_of_bir_unary_exp,
  type_of_bir_bin_exp,

  bir_cast_REWRS,
  bir_lcast_def,
  bir_hcast_REWRS,
  bir_scast_REWRS,

  type_of_bir_gencast,
  bir_gencast_ID,
  bir_casts_ID,
  bir_casts_Bit1,
  type_of_bir_casts
];


val bir_SIMPLE_REWRS_mem_exp = rewrites [
  bir_number_of_mem_splits_REWRS,
  bir_number_of_mem_splits_NEQ_SOME0,
  bir_number_of_mem_splits_ID,
  bir_number_of_mem_splits_EQ_SOME1,

  type_of_bir_mem_concat,
  type_of_bir_load_from_mem,
  bir_load_from_mem_NONE_REWRS,
  bir_load_from_mem_EQ_NONE_IMP,

  bir_load_from_mem_used_addrs_REWRS,
  bir_load_from_mem_used_addrs_FINITE,
  bir_load_from_mem_used_addrs_EMPTY,

  bir_store_in_mem_NONE_REWRS,
  bir_store_in_mem_EQ_NONE_IMP,
  bir_store_in_mem_used_addrs_REWRS,
  bir_store_in_mem_used_addrs_FINITE,
  bir_store_in_mem_used_addrs_EMPTY
];


val bir_SIMPLE_REWRS_values = rewrites [
  bir_val_checker_REWRS,
  type_of_bir_val_def,
  bir_type_checker_REWRS,
  bir_type_is_Bool_IMPL,
  bir_dest_bool_val_EQ_SOME,
  bir_dest_bool_val_EQ_NONE,
  bir_dest_bool_val_bool2b
];

val bir_SIMPLE_REWRS_exp = rewrites [
  bir_eval_exp_def,
  bir_eval_cast_REWRS,
  bir_eval_unary_exp_REWRS,
  bir_eval_bin_exp_REWRS,
  bir_eval_bin_pred_REWRS,
  bir_eval_ifthenelse_REWRS,
  bir_eval_ifthenelse_REWRS_Unknown,
  bir_eval_load_Unknown_REWRS,
  bir_eval_store_Unknown_REWRS
];

val bir_SIMPLE_REWRS_program = rewrites [
  bir_state_is_terminated_IMP,
  bir_declare_initial_value_def,
  IS_BER_Ended_def,
  bir_block_pc_11
];

val bir_SIMPLE_REWRS_typing_exp = rewrites [
  type_of_bir_exp_EQ_SOME_REWRS,
  type_of_bir_exp_EQ_NONE_REWRS,
  bir_vars_of_exp_def,
  valOf_BER_Ended_def,
  valOf_BER_Ended_steps_def
];

val bir_SIMPLE_REWRS_ss = simpLib.merge_ss [
  bir_TYPES_ss,
  bir_SIMPLE_REWRS_imm,
  bir_SIMPLE_REWRS_values,
  bir_SIMPLE_REWRS_env,
  bir_SIMPLE_REWRS_imm_exp,
  bir_SIMPLE_REWRS_mem_exp,
  bir_SIMPLE_REWRS_exp,
  bir_SIMPLE_REWRS_program,
  bir_SIMPLE_REWRS_typing_exp
];

val holBACore_ss = bir_SIMPLE_REWRS_ss;

end
