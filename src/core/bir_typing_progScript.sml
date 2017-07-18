open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_typing_expTheory bir_programTheory;
open wordsLib;

val _ = new_theory "bir_typing_prog";


(* ------------------------------------------------------------------------- *)
(*  Programs                                                                 *)
(* ------------------------------------------------------------------------- *)

val bir_is_well_typed_stmtE_def = Define `
  (bir_is_well_typed_stmtE (BStmt_Jmp _) = T) /\
  (bir_is_well_typed_stmtE (BStmt_CJmp c _ _) = (type_of_bir_exp c = SOME BType_Bool)) /\
  (bir_is_well_typed_stmtE (BStmt_Halt e) = (type_of_bir_exp e <> NONE))`

val bir_is_well_typed_stmtB_def = Define `
  (bir_is_well_typed_stmtB (BStmt_Declare _) = T) /\
  (bir_is_well_typed_stmtB (BStmt_Assign v e) = (type_of_bir_exp e = SOME (bir_var_type v))) /\
  (bir_is_well_typed_stmtB (BStmt_Assert e) = (type_of_bir_exp e = SOME BType_Bool)) /\
  (bir_is_well_typed_stmtB (BStmt_Assume e) = (type_of_bir_exp e = SOME BType_Bool))`;

val bir_is_well_typed_stmt_def = Define `
  (bir_is_well_typed_stmt (BStmtE s) = bir_is_well_typed_stmtE s) /\
  (bir_is_well_typed_stmt (BStmtB s) = bir_is_well_typed_stmtB s)`;

val bir_is_well_typed_block_def = Define `bir_is_well_typed_block bl <=>
  ((EVERY bir_is_well_typed_stmtB bl.bb_statements) /\ 
   (bir_is_well_typed_stmtE bl.bb_last_statement))`;

val bir_is_well_typed_program_def = Define `bir_is_well_typed_program (BirProgram p) <=>
  (EVERY bir_is_well_typed_block p)`;


val bir_get_current_statement_well_typed = store_thm ("bir_get_current_statement_well_typed",
  ``!p pc stmt. (bir_is_well_typed_program p /\
                (bir_get_current_statement p pc = SOME stmt)) ==>
                bir_is_well_typed_stmt stmt``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_well_typed_program_def, bir_get_current_statement_def] >>
GEN_TAC >>
Cases_on `(bir_get_program_block_info_by_label (BirProgram p) pc.bpc_label)` >- (
  ASM_SIMP_TAC std_ss []
) >>
rename1 `_ = SOME xy` >> Cases_on `xy` >>
rename1 `_ = SOME (i, bl)` >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [] >>
Cases_on `EVERY bir_is_well_typed_block p` >> ASM_SIMP_TAC std_ss [] >>
`bir_is_well_typed_block bl` by (
  `MEM bl p` by METIS_TAC [bir_get_program_block_info_by_label_THM, listTheory.MEM_EL] >>
  METIS_TAC[listTheory.EVERY_MEM]
) >>
CASE_TAC >> (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def, bir_is_well_typed_stmt_def]
) >>
METIS_TAC[listTheory.EVERY_MEM, listTheory.MEM_EL]);


val _ = export_theory();
