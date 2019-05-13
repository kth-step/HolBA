structure HolBASimps :> HolBASimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_typing_progTheory;
open bir_typing_expTheory;
open HolBACoreSimps;

open listTheory;
open pred_setTheory;


val bir_vars_of_exp_thms = [bir_vars_of_exp_def, bir_vars_of_label_exp_def]
val bir_vars_of_stmt_thms = [bir_vars_of_stmt_def, bir_vars_of_stmtE_def, bir_vars_of_stmtB_def];
val bir_stmts_of_prog_thms = [bir_stmts_of_prog_def, bir_stmts_of_block_def];

val aux_thms = [LIST_TO_SET, combinTheory.K_THM];
val pred_set_thms = [IMAGE_INSERT, IMAGE_EMPTY, BIGUNION_INSERT, BIGUNION_EMPTY, UNION_EMPTY, INSERT_UNION_EQ];


val stmts_of_prog_ss = rewrites (bir_TYPES_thms@bir_stmts_of_prog_thms@aux_thms@pred_set_thms);
val vars_of_prog_ss = rewrites (bir_TYPES_thms@[bir_vars_of_program_ALT_DEF]@bir_vars_of_exp_thms@
                                bir_vars_of_stmt_thms@bir_stmts_of_prog_thms@aux_thms@pred_set_thms);


end
