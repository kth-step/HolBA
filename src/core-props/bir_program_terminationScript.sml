open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_program_valid_stateTheory HolBACoreSimps;


val _ = new_theory "bir_program_termination";


(* ------------------------------------------------------------------------- *)
(* This theory tries to reason about which possible ways there are for a     *)
(* program to terminate                                                      *)
(* ------------------------------------------------------------------------- *)

(* TODO: extend this significantly *)


val bir_exec_stmtB_not_halted_jumped = store_thm ("bir_exec_stmtB_not_halted_jumped",
``(!st stmt l. (st.bst_status <> BST_JumpOutside l) ==> ((bir_exec_stmtB stmt st).bst_status <> BST_JumpOutside l)) /\
  (!st stmt v. (st.bst_status <> BST_Halted v) ==> ((bir_exec_stmtB stmt st).bst_status <> BST_Halted v))``,

CONJ_TAC >> Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_state_set_failed_def]
));


val bir_exec_stmtB_terminates_no_change = store_thm ("bir_exec_stmtB_terminates_no_change",
``!st stmt. ~(bir_state_is_terminated st) ==>
              (bir_state_is_terminated (bir_exec_stmtB stmt st)) ==>
              (((bir_exec_stmtB stmt st) with bst_status := BST_Running) = st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
  bir_state_t_component_equality, bir_exec_stmtB_pc_unchanged] >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_state_set_failed_def,
    bir_state_is_terminated_def]
));


val bir_exec_stmtE_terminates_no_change = store_thm ("bir_exec_stmtE_terminates_no_change",
``!p st stmt. ~(bir_state_is_terminated st) ==>
              (bir_state_is_terminated (bir_exec_stmtE p stmt st)) ==>
              (((bir_exec_stmtE p stmt st) with bst_status := BST_Running) = st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
  bir_state_t_component_equality, bir_exec_stmtB_pc_unchanged] >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def, LET_DEF, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_jmp_def, bir_exec_stmt_halt_def] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_state_set_failed_def]
));


val _ = export_theory();
