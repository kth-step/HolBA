structure HolBASimps :> HolBASimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listTheory;
open pred_setTheory;

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


end
