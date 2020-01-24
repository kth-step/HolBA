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


val bir_TYPES_thms = (flatten (map type_rws bir_list_of_types));

val bir_TYPES_ss = rewrites bir_TYPES_thms;

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
  bir_env_write_different_type
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
  bir_eval_memeq_REWRS,

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
  bir_dest_bool_val_bool2b,
  bir_dest_bool_val_opt_EQ_SOME,
  bir_dest_bool_val_opt_EQ_NONE,
  bir_dest_bool_val_opt_bool2b
];

val bir_SIMPLE_REWRS_exp = rewrites [
  bir_eval_exp_def,
  bir_eval_cast_REWRS,
  bir_eval_unary_exp_REWRS,
  bir_eval_bin_exp_REWRS,
  bir_eval_bin_pred_REWRS,
  bir_eval_ifthenelse_REWRS,
  bir_eval_ifthenelse_REWRS_NONE,
  bir_eval_load_NONE_REWRS,
  bir_eval_store_NONE_REWRS
];

val bir_SIMPLE_REWRS_program = rewrites [
  bir_state_is_terminated_IMP,
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


(* TODO: These should only be defined once in HolBA... *)
val string_ss = rewrites (type_rws ``:string``);
val char_ss = rewrites (type_rws ``:char``);

val simp_conv_for_bir_var_set_is_well_typed =
  ((* first, convert the set to a list *)
    (RAND_CONV (REWRITE_CONV [pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]))
    THENC
    REPEATC (
      (fn x => REWRITE_CONV [Once UNION_INSERT] x)
      THENC (
	(RATOR_CONV o LAND_CONV) (
	  (REWRITE_CONV [pred_setTheory.IN_INSERT])
	  THENC
	  (SIMP_CONV (std_ss++holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss)
	    [pred_setTheory.NOT_IN_EMPTY])
	)
      )
    ) THENC
    REWRITE_CONV [pred_setTheory.UNION_EMPTY]
  ) THENC
  (REWRITE_CONV [GSYM listTheory.LIST_TO_SET])
  THENC
  (* normalize to bir_var_set_is_well_typed *)
  (REWRITE_CONV [GSYM bir_env_oldTheory.bir_var_set_is_well_typed_EQ_bir_vs_consistent])
  THENC
  (* then, repeatedly check for inconsistency of the first list element with the rest *)
  REPEATC (
    (fn x => REWRITE_CONV [Once bir_env_oldTheory.bir_var_set_is_well_typed_REWRS] x)
    THENC
    (LAND_CONV EVAL) THENC
    (REWRITE_CONV [])
  ) THENC
  (* and finish when the end of the list is reached *)
  (REWRITE_CONV [bir_env_oldTheory.bir_var_set_is_well_typed_REWRS]
);

val bir_var_set_is_well_typed_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K simp_conv_for_bir_var_set_is_well_typed),
                    key= SOME ([], ``bir_var_set_is_well_typed varset``),
                    name = "simp_conv_for_bir_var_set_is_well_typed",
                    trace = 2}],
          dprocs = [],
          filter = NONE,
          name = SOME "bir_var_set_is_well_typed_ss",
          rewrs = []};

val bir_inter_var_set_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K computeLib.EVAL_CONV),
                    key= SOME ([], ``A INTER B``),
                    name = "EVAL_CONV_INTER",
                    trace = 2}],
                    dprocs = [],
          filter = NONE,
          name = SOME "bir_inter_var_set_ss",
          rewrs = []};

val bir_union_var_set_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K computeLib.EVAL_CONV),
                    key= SOME ([], ``A UNION B``),
                    name = "EVAL_CONV_UNION",
                    trace = 2}],
          dprocs = [],
          filter = NONE,
          name = SOME "bir_union_var_set_ss",
          rewrs = []};



end
