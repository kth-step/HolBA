structure HolBASimps :> HolBASimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listTheory;
open pred_setTheory;

open bir_immTheory;
open bir_envTheory;
open bir_exp_memTheory;
open bir_typing_progTheory;
open bir_typing_expTheory;
open bir_valuesTheory;
open bir_bool_expTheory;
open bir_nzcv_expTheory;
open bir_extra_expsTheory;
open bir_interval_expTheory;
open HolBACoreSimps;


val bir_vars_of_exp_thms = [bir_vars_of_exp_def, bir_vars_of_label_exp_def]
val bir_vars_of_stmt_thms = [bir_vars_of_stmt_def, bir_vars_of_stmtE_def, bir_vars_of_stmtB_def];
val bir_stmts_of_prog_thms = [bir_stmts_of_prog_def, bir_stmts_of_block_def];

val aux_thms = [LIST_TO_SET, combinTheory.K_THM, BType_Bool_def];
val pred_set_thms = [IMAGE_INSERT, IMAGE_EMPTY, BIGUNION_INSERT, BIGUNION_EMPTY, UNION_EMPTY, INSERT_UNION_EQ];
val common_exp_defs = [bir_exp_false_def, bir_exp_true_def,
                       (* Use vars_of theorems to avoid unfolding cumbersome definitions *)
                       (* from bir_nzcv_expTheory *)
                       BExp_nzcv_ADD_vars_of,
                       BExp_nzcv_SUB_vars_of,
                       BExp_ADD_WITH_CARRY_vars_of,
                       (* from bir_extra_expsTheory *)
                       BExp_Align_vars_of,
                       BExp_Aligned_vars_of,
                       BExp_word_reverse_vars_of,
                       BExp_MSB_vars_of,
                       BExp_LSB_vars_of,
                       BExp_word_bit_vars_of,
                       BExp_word_bit_exp_vars_of,
                       BExp_ror_vars_of,
                       BExp_ror_exp_vars_of,
                       BExp_rol_vars_of, 
                       BExp_rol_exp_vars_of,
                       BExp_extr_vars_of,
                       (* from bir_interval_expTheory *)
                       BExp_unchanged_mem_interval_distinct_vars_of];


val STMTS_OF_PROG_ss = rewrites (bir_TYPES_thms@bir_stmts_of_prog_thms@aux_thms@pred_set_thms);
val VARS_OF_PROG_ss = rewrites (bir_TYPES_thms@[bir_vars_of_program_ALT_DEF]@bir_vars_of_exp_thms@
                                bir_vars_of_stmt_thms@bir_stmts_of_prog_thms@aux_thms@pred_set_thms@
                                common_exp_defs);

(* Simpset for computing bir_is_bool_exp of BIR expressions *)
local
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
in
  val bir_is_bool_ss = simpLib.merge_ss [type_thms, thms];
end;

(* Useful when simplifying bir_env_read. *)
val bir_type_val_opt_ss =
  DatatypeSimps.case_cong_ss [``:bir_type_t # bir_val_t option``];


end
