open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory
open bir_programTheory HolBACoreSimps;


val _ = new_theory "bir_program_env_order";



(* ------------------------------------------------------------------------- *)
(*  End statements do not modify the environment                             *)
(* ------------------------------------------------------------------------- *)


val bir_exec_stmtE_env_unchanged = store_thm ("bir_exec_stmtE_env_unchanged",
``!p st stmt. (bir_exec_stmtE p stmt st).bst_environ = st.bst_environ``,

REPEAT GEN_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [
    bir_exec_stmtE_def, LET_DEF, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_jmp_def, bir_exec_stmt_halt_def, bir_state_set_failed_def] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) []
));

(* ------------------------------------------------------------------------- *)
(*  Only declare and assign update the environment                           *)
(* ------------------------------------------------------------------------- *)

val bir_state_set_failed_SAME_ENV = store_thm ("bir_state_set_failed_SAME_ENV",
  ``!st. (bir_state_set_failed st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]);

val bir_exec_stmt_assume_SAME_ENV = store_thm("bir_exec_stmt_assume_SAME_ENV",
  ``!e st. (bir_exec_stmt_assume e st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assume_def] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> SIMP_TAC (std_ss++holBACore_ss) [
   bir_state_set_failed_SAME_ENV]
);


val bir_exec_stmt_assert_SAME_ENV = store_thm("bir_exec_stmt_assert_SAME_ENV",
  ``!e st. (bir_exec_stmt_assert e st).bst_environ = st.bst_environ``,
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assert_def] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> SIMP_TAC (std_ss++holBACore_ss) [
   bir_state_set_failed_SAME_ENV]
);



(* ------------------------------------------------------------------------- *)
(*  However, declare and assign only extend the environment                  *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmt_declare_ENV = store_thm("bir_exec_stmt_declare_ENV",
  ``!vn vty st. (bir_exec_stmt_declare vn vty st).bst_environ =
      if (bir_env_varname_is_bound st.bst_environ vn) then st.bst_environ else
      THE (bir_env_update vn (bir_declare_initial_value vty) vty
            st.bst_environ)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_declare_def, LET_DEF] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [
     bir_state_set_failed_SAME_ENV]
) >>
Cases_on `st.bst_environ` >> Cases_on `vty` >> (
  FULL_SIMP_TAC std_ss [bir_env_update_def, bir_declare_initial_value_def,
     type_of_bir_val_def]
));


val bir_exec_stmt_assign_ENV = store_thm("bir_exec_stmt_assign_ENV",
  ``!v e st.
      (bir_exec_stmt_assign v e st).bst_environ =
      (case bir_env_write v (bir_eval_exp e st.bst_environ) st.bst_environ of
         | SOME env => env
         | NONE => st.bst_environ)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assign_def, LET_DEF] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC >> (
   ASM_SIMP_TAC (std_ss++holBACore_ss) [
     bir_state_set_failed_SAME_ENV]
));


(* ------------------------------------------------------------------------- *)
(*  Therefore, executing steps only extentends the environment               *)
(* ------------------------------------------------------------------------- *)

val bir_exec_stmt_ENV_ORDER = store_thm ("bir_exec_stmt_ENV_ORDER",
``!p st stmt. bir_env_order st.bst_environ (bir_exec_stmt p stmt st).bst_environ``,

Tactical.REVERSE (Cases_on `stmt`) >- (
  SIMP_TAC std_ss [bir_exec_stmtE_env_unchanged, bir_exec_stmt_def, bir_env_order_REFL]
) >>
rename1 `BStmtB stmt` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [bir_exec_stmt_def, LET_DEF,
   bir_env_order_REFL] >>
GEN_TAC >> Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtB_def,
    bir_exec_stmt_assert_SAME_ENV, bir_exec_stmt_assume_SAME_ENV,
    bir_env_order_REFL, bir_exec_stmt_assign_ENV,  bir_exec_stmt_declare_ENV]
) >- (
  rename1 `bir_var_name v` >>
  Cases_on `bir_env_varname_is_bound st.bst_environ (bir_var_name v)` >> ASM_REWRITE_TAC[bir_env_order_REFL] >>
  `?env'. bir_env_update (bir_var_name v)
            (bir_declare_initial_value (bir_var_type v)) (bir_var_type v)
            st.bst_environ = SOME env'` by (
    Cases_on `st.bst_environ` >> Cases_on `bir_var_type v` >> (
      ASM_SIMP_TAC std_ss [bir_declare_initial_value_def, bir_env_update_def,
        type_of_bir_val_def]
    )
  ) >>
  ASM_SIMP_TAC std_ss [] >>
  METIS_TAC[bir_env_order_update]
) >- (
  REPEAT STRIP_TAC >>
  Cases_on `bir_env_write b (bir_eval_exp b0 st.bst_environ) st.bst_environ` >> (
    ASM_SIMP_TAC std_ss [bir_env_order_REFL]
  ) >>
  METIS_TAC [bir_env_order_write]
));


val bir_exec_step_ENV_ORDER = store_thm ("bir_exec_step_ENV_ORDER",
``!p st. bir_env_order st.bst_environ (bir_exec_step p st).bst_environ``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_step_def] >>
REPEAT CASE_TAC >> (
  SIMP_TAC (std_ss++holBACore_ss) [bir_env_order_REFL, bir_state_set_failed_SAME_ENV,
    bir_exec_stmt_ENV_ORDER]
));



val bir_exec_step_FUNPOW_ENV_ORDER = store_thm ("bir_exec_step_FUNPOW_ENV_ORDER",
``!p n st. bir_env_order st.bst_environ (FUNPOW (bir_exec_step p) n st).bst_environ``,

GEN_TAC >>
Induct >> (
  SIMP_TAC std_ss [arithmeticTheory.FUNPOW, bir_env_order_REFL]
) >>
GEN_TAC >>
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_env_order_TRANS) >>
Q.EXISTS_TAC `(bir_exec_step p st).bst_environ` >>
ASM_SIMP_TAC std_ss [bir_exec_step_ENV_ORDER]);



val bir_exec_steps_ENV_ORDER = store_thm ("bir_exec_steps_ENV_ORDER",
``!p c st st'. (bir_exec_steps p st = SOME (c, st')) ==>
  bir_env_order st.bst_environ st'.bst_environ``,

SIMP_TAC std_ss [bir_exec_steps_EQ_SOME, bir_exec_step_FUNPOW_ENV_ORDER]);


val bir_exec_step_n_ENV_ORDER = store_thm ("bir_exec_step_n_ENV_ORDER",
``!p c n st st'. (bir_exec_step_n p st n = (c, st')) ==>
  bir_env_order st.bst_environ st'.bst_environ``,

SIMP_TAC std_ss [bir_exec_step_n_EQ_THM, bir_exec_step_FUNPOW_ENV_ORDER]);


val _ = export_theory();
