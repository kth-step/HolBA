open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory
open bir_envTheory bir_valuesTheory
open bir_programTheory HolBACoreSimps;


val _ = new_theory "bir_program_valid_state";


(* -------------------------------------------------------------------------
   We call a program valid, if all its labels are distinct and it is not empty
   ------------------------------------------------------------------------- *)

val bir_is_valid_labels_def = Define `bir_is_valid_labels p =
  ALL_DISTINCT (bir_labels_of_program p)`;

val bir_is_valid_program_def = Define `bir_is_valid_program p <=>
   (bir_is_valid_labels p) /\ ~(p = BirProgram [])`;


(* This allows some nice rewrites *)
val bir_is_valid_labels_blocks_EQ_EL = store_thm ("bir_is_valid_labels_blocks_EQ_EL",
  ``!p n1 n2. (bir_is_valid_labels (BirProgram p) /\ n1 < LENGTH p /\ n2 < LENGTH p /\
                ((EL n1 p).bb_label = (EL n2 p).bb_label)) ==> (n1 = n2)``,

SIMP_TAC list_ss [bir_is_valid_labels_def, bir_labels_of_program_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.ISPEC `MAP (\bl. bl.bb_label) (p:('a bir_block_t) list)` listTheory.EL_ALL_DISTINCT_EL_EQ) >>
ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `n1` >> Q.EXISTS_TAC `n2` >>
ASM_SIMP_TAC list_ss [listTheory.EL_MAP]);


val bir_is_valid_labels_blocks_EQ = store_thm ("bir_is_valid_labels_blocks_EQ",
  ``!p bl1 bl2. (bir_is_valid_labels (BirProgram p) /\ MEM bl1 p /\ MEM bl2 p /\
                (bl1.bb_label = bl2.bb_label)) ==> (bl1 = bl2)``,

METIS_TAC [listTheory.MEM_EL, bir_is_valid_labels_blocks_EQ_EL]);


val bir_get_program_block_info_by_label_valid_THM = store_thm ("bir_get_program_block_info_by_label_valid_THM",
  ``(!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl. bir_is_valid_labels (BirProgram p) ==>
          ((bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
           ((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l)))``,

SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_get_program_block_info_by_label_def,
  INDEX_FIND_EQ_NONE, listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0] >>
REPEAT STRIP_TAC >>
`j' < LENGTH p` by DECIDE_TAC >>
`j' = i` by METIS_TAC[bir_is_valid_labels_blocks_EQ_EL] >>
FULL_SIMP_TAC arith_ss []);



(* -------------------------------------------------------------------------
   Next we define what we mean by a PC being valid.
   Later this is then used to define valid states
   ------------------------------------------------------------------------- *)

val bir_is_valid_pc_def = Define `bir_is_valid_pc p pc =
   (?i bl. (bir_get_program_block_info_by_label p (pc.bpc_label) = SOME (i, bl)) /\
           (pc.bpc_index <= LENGTH bl.bb_statements))`;

val bir_is_valid_pc_of_valid_blocks = store_thm ("bir_is_valid_pc_of_valid_blocks",
  ``!p pc. bir_is_valid_labels (BirProgram p) ==>
           (bir_is_valid_pc (BirProgram p) pc <=> (?bl. MEM bl p /\ (pc.bpc_label = bl.bb_label) /\
             (pc.bpc_index <= LENGTH bl.bb_statements)))``,
SIMP_TAC std_ss [bir_is_valid_pc_def, bir_get_program_block_info_by_label_valid_THM,
  listTheory.MEM_EL, GSYM LEFT_EXISTS_AND_THM] >>
METIS_TAC[]);


val bir_get_program_block_info_by_label_valid_pc = store_thm ("bir_get_program_block_info_by_label_valid_pc",
  ``!p pc. bir_is_valid_pc p pc ==> IS_SOME (bir_get_program_block_info_by_label p pc.bpc_label)``,

SIMP_TAC std_ss [bir_is_valid_pc_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_get_current_statement_IS_SOME = store_thm ("bir_get_current_statement_IS_SOME",
  ``!p pc. IS_SOME (bir_get_current_statement p pc) <=> bir_is_valid_pc p pc``,

REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def, bir_is_valid_pc_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) []);



(* -------------------------------------------------------------------------
   The next PC is valid iff and only if the current one is valid and pointing
   to a basic statement
   ------------------------------------------------------------------------- *)

val bir_get_current_statement_SOME_B = store_thm ("bir_get_current_statement_SOME_B",
  ``!p pc stmt. (bir_get_current_statement p pc = SOME (BStmtB stmt)) <=>
                (?i bl. (bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl)) /\
                   (pc.bpc_index < LENGTH bl.bb_statements) /\
                   (stmt = EL pc.bpc_index bl.bb_statements))``,

REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [] >>
METIS_TAC[]);


val bir_get_current_statement_SOME_E = store_thm ("bir_get_current_statement_SOME_E",
  ``!p pc stmt. (bir_get_current_statement p pc = SOME (BStmtE stmt)) <=>
                (?i bl. (bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl)) /\
                   (pc.bpc_index = LENGTH bl.bb_statements) /\
                   (stmt = bl.bb_last_statement))``,

REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) []);


val bir_pc_next_valid = store_thm ("bir_pc_next_valid",
``!p pc. (bir_is_valid_pc p (bir_pc_next pc)) <=>
         (?stmt. bir_get_current_statement p pc = SOME (BStmtB stmt))``,

REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_def, bir_pc_next_def,
  bir_get_current_statement_SOME_B, GSYM arithmeticTheory.LESS_EQ]);



(* -------------------------------------------------------------------------
   The block PC is valid iff the label exists, therefore, the first pc is
   valid for all valid programs
   ------------------------------------------------------------------------- *)

val bir_is_valid_pc_block_pc = store_thm ("bir_is_valid_pc_block_pc",
``!l p. bir_is_valid_pc p (bir_block_pc l) <=>
        MEM l (bir_labels_of_program p)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_def,
  bir_get_program_block_info_by_label_MEM, bir_block_pc_def]);


val bir_pc_first_valid = store_thm ("bir_pc_first_valid",
  ``!p. bir_is_valid_program p ==> bir_is_valid_pc p (bir_pc_first p)``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_pc_first_def, bir_is_valid_pc_block_pc] >>
Cases_on `p` >> (
  SIMP_TAC list_ss [bir_is_valid_program_def, bir_labels_of_program_def]
));


val bir_is_valid_pc_label_OK = store_thm ("bir_is_valid_pc_label_OK",
  ``!p pc. bir_is_valid_pc p pc ==> MEM pc.bpc_label (bir_labels_of_program p)``,

Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_valid_pc_def, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_labels_of_program_def,
  bir_get_program_block_info_by_label_THM] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM] >>
METIS_TAC[]);



(* -------------------------------------------------------------------------
   Finally, we can define what a valid state is.

   A valid state has a well-typed environment and a valid PC
   ------------------------------------------------------------------------- *)

val bir_is_valid_state_def = Define `bir_is_valid_state p st <=>
  ((bir_is_well_typed_env st.bst_environ) /\ bir_is_valid_pc p st.bst_pc)`;

(* The initial state is valid for all valid programs *)
val bir_state_init_valid = store_thm ("bir_state_init_valid",
  ``!p. bir_is_valid_program p ==> bir_is_valid_state p (bir_state_init p)``,

SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_is_valid_state_def, bir_state_init_def,
  bir_pc_first_valid, bir_is_well_typed_env_empty]);

(* valid states allow some nice rewrite for bir_exec_step *)
val bir_exec_step_valid_THM = store_thm ("bir_exec_step_valid_THM",
 ``!p st. bir_is_valid_state p st ==>
          (if bir_state_is_terminated st then
             (bir_exec_step p st = (NONE, st))
           else
             (bir_is_valid_pc p st.bst_pc) /\
             (?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                     (bir_exec_step p st = (bir_exec_stmt p stmt st))))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_step_def, bir_is_valid_state_def] >>
Cases_on `bir_state_is_terminated st` >> ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] >>
`IS_SOME (bir_get_current_statement p st.bst_pc)` suffices_by METIS_TAC[optionTheory.IS_SOME_EXISTS] >>
FULL_SIMP_TAC std_ss [bir_get_current_statement_IS_SOME,
  bir_is_valid_state_def]);


val bir_exec_step_state_valid_THM = store_thm ("bir_exec_step_state_valid_THM",
 ``!p st. bir_is_valid_state p st ==>
          (if bir_state_is_terminated st then
             (bir_exec_step_state p st = st)
           else
             (bir_is_valid_pc p st.bst_pc) /\
             (?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                     (bir_exec_step_state p st = (bir_exec_stmt_state p stmt st))))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`] bir_exec_step_valid_THM) >>
ASM_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_stmt_state_def] >>
METIS_TAC [pairTheory.SND]);


(* -------------------------------------------------------------------------
   bir_is_valid_state is an invariant
   ------------------------------------------------------------------------- *)

val bir_is_valid_state_set_failed = prove (
  ``!p st. bir_is_valid_state p st ==>
           bir_is_valid_state p (bir_state_set_failed st)``,
SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_is_valid_state_def, bir_state_set_failed_def]);


val bir_exec_stmtB_valid_state_invar_declare = prove (
  ``!p st v ty. bir_is_valid_state p st ==>
                bir_is_valid_state p (bir_exec_stmt_declare v ty st)``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_stmt_declare_def, LET_THM,
  bir_is_valid_state_set_failed, bir_var_type_def, bir_var_name_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_env_varname_is_bound st.bst_environ v` >> ASM_REWRITE_TAC[] >>

`?env. (bir_env_update v (bir_declare_initial_value ty) ty st.bst_environ = SOME env)` by (
  Cases_on `st.bst_environ` >>
  Cases_on `ty` >> (
    FULL_SIMP_TAC std_ss [bir_declare_initial_value_def, type_of_bir_val_def, bir_env_update_def]
  )
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_state_def] >>
METIS_TAC[bir_env_update_is_well_typed_env]);


val bir_exec_stmtB_valid_state_invar_assign = prove (
  ``!p st v ex. bir_is_valid_state p st ==>
                bir_is_valid_state p (bir_exec_stmt_assign v ex st)``,
Cases_on `v` >> rename1 `BVar v ty` >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_stmt_assign_def, LET_THM] >>
Cases_on `bir_env_write (BVar v ty) (bir_eval_exp ex st.bst_environ)
       st.bst_environ` >> (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_state_def] >>
METIS_TAC[bir_env_write_is_well_typed_env]);


val bir_exec_stmtB_valid_state_invar_assert = prove (
  ``!p st ex. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmt_assert ex st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assert_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
REPEAT CASE_TAC >> (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
));


val bir_exec_stmtB_valid_state_invar_assume = prove (
  ``!p st ex. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmt_assume ex st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assume_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
REPEAT CASE_TAC >> (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_state_def]);


val bir_exec_stmtB_valid_state_invar_observe = prove (
  ``!p st ec.
      bir_is_valid_state p st ==>
      bir_is_valid_state p (bir_exec_stmt_observe_state ec st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_observe_state_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
REPEAT CASE_TAC >> (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
));


val bir_exec_stmtB_valid_state_invar = store_thm ("bir_exec_stmtB_valid_state_invar",
``!p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtB_state stmt st)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_state_REWRS,
    bir_exec_stmtB_valid_state_invar_declare,
    bir_exec_stmtB_valid_state_invar_assign,
    bir_exec_stmtB_valid_state_invar_assume,
    bir_exec_stmtB_valid_state_invar_assert,
    bir_exec_stmtB_valid_state_invar_observe]
));


val bir_exec_stmtB_pc_unchanged = store_thm ("bir_exec_stmtB_pc_unchanged",
``!st stmt. (bir_exec_stmtB_state stmt st).bst_pc = st.bst_pc``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_state_REWRS, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_state_def] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
));


val bir_exec_stmt_jmp_to_label_valid_state_invar = store_thm ("bir_exec_stmt_jmp_to_label_valid_state_invar",
  ``!p st l. bir_is_valid_state p st ==>
             bir_is_valid_state p (bir_exec_stmt_jmp_to_label p l st)``,
SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_state_def,
    bir_is_valid_pc_block_pc],

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_state_def]
]);


val bir_exec_stmt_jmp_valid_state_invar = store_thm ("bir_exec_stmt_jmp_valid_state_invar",
  ``!p st l. bir_is_valid_state p st ==>
             bir_is_valid_state p (bir_exec_stmt_jmp p l st)``,
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >> CASE_TAC >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_valid_state_invar,
                       bir_is_valid_state_set_failed]
));


val bir_exec_stmtE_valid_state_invar_jmp = prove (
  ``!p st l. bir_is_valid_state p st ==>
             bir_is_valid_state p (bir_exec_stmtE p (BStmt_Jmp l) st)``,
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_valid_state_invar]);


val bir_exec_stmtE_valid_state_invar_cjmp = prove (
  ``!p st ex l1 l2.
       bir_is_valid_state p st ==>
       bir_is_valid_state p (bir_exec_stmtE p (BStmt_CJmp ex l1 l2) st)``,
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_dest_bool_val (bir_eval_exp ex st.bst_environ)` >- (
  ASM_SIMP_TAC std_ss [bir_is_valid_state_set_failed]
) >>
rename1 `SOME c` >>
Cases_on `c` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_jmp_valid_state_invar]
));


val bir_exec_stmtE_valid_state_invar_halt = prove (
  ``!p st ex.  bir_is_valid_state p st ==>
               bir_is_valid_state p (bir_exec_stmtE p (BStmt_Halt ex) st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_halt_def,
  bir_is_valid_state_def]);


val bir_exec_stmtE_valid_state_invar = store_thm ("bir_exec_stmtE_valid_state_invar",
``!p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtE p stmt st)``,

REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [
    bir_exec_stmtE_valid_state_invar_cjmp,
    bir_exec_stmtE_valid_state_invar_jmp,
    bir_exec_stmtE_valid_state_invar_halt]
));


val bir_exec_step_valid_state_invar = store_thm ("bir_exec_step_valid_state_invar",
``!p st. bir_is_valid_state p st ==>
         bir_is_valid_state p (bir_exec_step_state p st)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_step_state_valid_THM >>
Cases_on `bir_state_is_terminated st` >> FULL_SIMP_TAC std_ss [] >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, bir_exec_stmtE_valid_state_invar, LET_DEF]
) >>
rename1 `bir_exec_stmtB_state stmt st` >>
Q.ABBREV_TAC `st' = bir_exec_stmtB_state stmt st` >>
`bir_is_valid_state p st'` by METIS_TAC[bir_exec_stmtB_valid_state_invar] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [] >>
`st'.bst_pc = st.bst_pc` by METIS_TAC[bir_exec_stmtB_pc_unchanged] >>
FULL_SIMP_TAC (arith_ss++holBACore_ss) [bir_is_valid_state_def,
  bir_get_current_statement_SOME_B, bir_is_valid_pc_def, bir_pc_next_def] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC arith_ss []);


val _ = export_theory();
