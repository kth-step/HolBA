open HolKernel Parse boolLib bossLib;
open holba_auxiliaryTheory
open bir_envTheory bir_valuesTheory
open bir_programTheory HolBACoreSimps;

val _ = new_theory "bir_program_valid_state";


(* -------------------------------------------------------------------------
   We call a program valid, if all its labels are distinct and it is not empty
   ------------------------------------------------------------------------- *)

Definition bir_is_valid_labels_def:
  bir_is_valid_labels p =
  ALL_DISTINCT (bir_labels_of_program p)
End

Definition bir_program_is_empty_def:
  bir_program_is_empty (BirProgram p) <=> NULL p
End

Definition bir_is_valid_program_def:
  bir_is_valid_program p <=>
   (bir_is_valid_labels p) /\ ~(bir_program_is_empty p)
End


(* This allows some nice rewrites *)
Theorem bir_is_valid_labels_blocks_EQ_EL:
  !p n1 n2. (bir_is_valid_labels (BirProgram p) /\ n1 < LENGTH p /\ n2 < LENGTH p /\
                ((EL n1 p).bb_label = (EL n2 p).bb_label)) ==> (n1 = n2)
Proof
SIMP_TAC list_ss [bir_is_valid_labels_def, bir_labels_of_program_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.ISPEC `MAP (\bl. bl.bb_label) (p:('a bir_block_t) list)` listTheory.EL_ALL_DISTINCT_EL_EQ) >>
ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `n1` >> Q.EXISTS_TAC `n2` >>
ASM_SIMP_TAC list_ss [listTheory.EL_MAP]
QED


Theorem bir_is_valid_labels_blocks_EQ:
  !p bl1 bl2. (bir_is_valid_labels (BirProgram p) /\ MEM bl1 p /\ MEM bl2 p /\
                (bl1.bb_label = bl2.bb_label)) ==> (bl1 = bl2)
Proof
METIS_TAC [listTheory.MEM_EL, bir_is_valid_labels_blocks_EQ_EL]
QED


Theorem bir_get_program_block_info_by_label_valid_THM:
  (!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bl.bb_label <> l)))) /\

    (!p l i bl. bir_is_valid_labels (BirProgram p) ==>
          ((bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
           ((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bl.bb_label = l)))
Proof
SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_get_program_block_info_by_label_def,
  INDEX_FIND_EQ_NONE, listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0] >>
REPEAT STRIP_TAC >>
`j' < LENGTH p` by DECIDE_TAC >>
`j' = i` by METIS_TAC[bir_is_valid_labels_blocks_EQ_EL] >>
FULL_SIMP_TAC arith_ss []
QED



(* -------------------------------------------------------------------------
   Next we define what we mean by a PC being valid.
   Later this is then used to define valid states
   ------------------------------------------------------------------------- *)

Definition bir_is_valid_pc_def:
  bir_is_valid_pc p pc =
   (?i bl. (bir_get_program_block_info_by_label p (pc.bpc_label) = SOME (i, bl)) /\
           (pc.bpc_index <= LENGTH bl.bb_statements))
End

Theorem bir_is_valid_pc_of_valid_blocks:
  !p pc. bir_is_valid_labels (BirProgram p) ==>
           (bir_is_valid_pc (BirProgram p) pc <=> (?bl. MEM bl p /\ (pc.bpc_label = bl.bb_label) /\
             (pc.bpc_index <= LENGTH bl.bb_statements)))
Proof
SIMP_TAC std_ss [bir_is_valid_pc_def, bir_get_program_block_info_by_label_valid_THM,
  listTheory.MEM_EL, GSYM LEFT_EXISTS_AND_THM] >>
METIS_TAC[]
QED


Theorem bir_get_program_block_info_by_label_valid_pc:
  !p pc. bir_is_valid_pc p pc ==> IS_SOME (bir_get_program_block_info_by_label p pc.bpc_label)
Proof
SIMP_TAC std_ss [bir_is_valid_pc_def, GSYM LEFT_FORALL_IMP_THM]
QED


Theorem bir_get_current_statement_IS_SOME:
  !p pc. IS_SOME (bir_get_current_statement p pc) <=> bir_is_valid_pc p pc
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def, bir_is_valid_pc_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss) []
QED



(* -------------------------------------------------------------------------
   The next PC is valid iff and only if the current one is valid and pointing
   to a basic statement
   ------------------------------------------------------------------------- *)

Theorem bir_get_current_statement_SOME_B:
  !p pc stmt. (bir_get_current_statement p pc = SOME (BStmtB stmt)) <=>
                (?i bl. (bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl)) /\
                   (pc.bpc_index < LENGTH bl.bb_statements) /\
                   (stmt = EL pc.bpc_index bl.bb_statements))
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [] >>
METIS_TAC[]
QED


Theorem bir_get_current_statement_SOME_E:
  !p pc stmt. (bir_get_current_statement p pc = SOME (BStmtE stmt)) <=>
                (?i bl. (bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl)) /\
                   (pc.bpc_index = LENGTH bl.bb_statements) /\
                   (stmt = bl.bb_last_statement))
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) []
QED


Theorem bir_pc_next_valid:
  !p pc. (bir_is_valid_pc p (bir_pc_next pc)) <=>
         (?stmt. bir_get_current_statement p pc = SOME (BStmtB stmt))
Proof
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_def, bir_pc_next_def,
  bir_get_current_statement_SOME_B, GSYM arithmeticTheory.LESS_EQ]
QED



(* -------------------------------------------------------------------------
   The block PC is valid iff the label exists, therefore, the first pc is
   valid for all valid programs
   ------------------------------------------------------------------------- *)

Theorem bir_is_valid_pc_block_pc:
  !l p. bir_is_valid_pc p (bir_block_pc l) <=>
        MEM l (bir_labels_of_program p)
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_def,
  bir_get_program_block_info_by_label_MEM, bir_block_pc_def]
QED


Theorem bir_pc_first_valid:
  !p. bir_is_valid_program p ==> bir_is_valid_pc p (bir_pc_first p)
Proof
Cases >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_pc_first_def, bir_is_valid_pc_block_pc] >>
Cases_on `p` >> (
  SIMP_TAC list_ss [bir_is_valid_program_def, bir_labels_of_program_def,
    bir_program_is_empty_def]
)
QED


Theorem bir_is_valid_pc_label_OK:
  !p pc. bir_is_valid_pc p pc ==> MEM pc.bpc_label (bir_labels_of_program p)
Proof
Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_valid_pc_def, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_labels_of_program_def,
  bir_get_program_block_info_by_label_THM] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM] >>
METIS_TAC[]
QED



(* -------------------------------------------------------------------------
   Finally, we can define what a valid state is.

   A valid state has a well-typed environment and a valid PC
   ------------------------------------------------------------------------- *)

Definition bir_is_valid_state_def:
  bir_is_valid_state p st <=>
  ((bir_is_well_typed_env st.bst_environ) /\ bir_is_valid_pc p st.bst_pc)
End

(* The initial state is valid for all valid programs *)
Theorem bir_state_init_valid:
  !p. bir_is_valid_program p ==> bir_is_valid_state p (bir_state_init p)
Proof
SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_is_valid_state_def, bir_state_init_def,
  bir_pc_first_valid, bir_env_oldTheory.bir_is_well_typed_env_THM]
QED


Theorem bir_exec_step_invalid_pc_THM:
  !p st. ~(bir_is_valid_pc p st.bst_pc) ==>
          (bir_exec_step p st = (NONE, if (bir_state_is_terminated st) then st else bir_state_set_failed st))
Proof
METIS_TAC[bir_exec_step_def, bir_get_current_statement_IS_SOME, optionTheory.option_CLAUSES]
QED


(* valid states allow some nice rewrite for bir_exec_step *)
Theorem bir_exec_step_valid_THM:
  !p st. bir_is_valid_pc p st.bst_pc ==>
          (if bir_state_is_terminated st then
             (bir_exec_step p st = (NONE, st))
           else
             (?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                     (bir_exec_step p st = (bir_exec_stmt p stmt st))))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_step_def] >>
Cases_on `bir_state_is_terminated st` >> ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] >>
`IS_SOME (bir_get_current_statement p st.bst_pc)` suffices_by METIS_TAC[optionTheory.IS_SOME_EXISTS] >>
FULL_SIMP_TAC std_ss [bir_get_current_statement_IS_SOME,
  bir_is_valid_state_def]
QED


Theorem bir_exec_step_state_valid_THM:
  !p st. bir_is_valid_pc p st.bst_pc ==>
          (if bir_state_is_terminated st then
             (bir_exec_step_state p st = st)
           else
             (?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                     (bir_exec_step_state p st = (bir_exec_stmt_state p stmt st))))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`] bir_exec_step_valid_THM) >>
ASM_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_stmt_state_def] >>
METIS_TAC [pairTheory.SND]
QED


(* -------------------------------------------------------------------------
   bir_is_valid_state is an invariant
   ------------------------------------------------------------------------- *)

Theorem bir_exec_stmtB_well_typed_env_assign[local]:
  !st v ex. bir_is_well_typed_env st.bst_environ ==>
              bir_is_well_typed_env (bir_exec_stmt_assign v ex st).bst_environ
Proof
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]
QED


Theorem bir_exec_stmtB_well_typed_env_assert[local]:
  !st ex. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmt_assert ex st).bst_environ
Proof
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]
QED


Theorem bir_exec_stmtB_well_typed_env_assume[local]:
  !st ex. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmt_assume ex st).bst_environ
Proof
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]
QED


Theorem bir_exec_stmtB_well_typed_env_observe[local]:
  !st el ec.
      bir_is_well_typed_env st.bst_environ ==>
      bir_is_well_typed_env (bir_exec_stmt_observe_state ec el st).bst_environ
Proof
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]
QED


Theorem bir_exec_stmtB_well_typed_env:
  !st stmt. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmtB_state stmt st).bst_environ
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_state_REWRS,
    bir_exec_stmtB_well_typed_env_assign,
    bir_exec_stmtB_well_typed_env_assume,
    bir_exec_stmtB_well_typed_env_assert,
    bir_exec_stmtB_well_typed_env_observe]
)
QED


Theorem bir_exec_stmtB_pc_unchanged:
  !st stmt. (bir_exec_stmtB_state stmt st).bst_pc = st.bst_pc
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_state_REWRS, LET_DEF,
    bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_state_def] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
)
QED

Theorem bir_exec_stmtB_valid_state_invar:
  !p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtB_state stmt st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_stmtB_pc_unchanged, bir_exec_stmtB_well_typed_env]
QED


Theorem bir_exec_stmt_jmp_to_label_valid_pc:
  !p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmt_jmp_to_label p l st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_block_pc],

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
QED


Theorem bir_exec_stmt_jmp_valid_pc:
  !p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmt_jmp p l st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >> CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [
     bir_exec_stmt_jmp_to_label_valid_pc,
     bir_state_set_typeerror_def]
)
QED


Theorem bir_exec_stmtE_valid_pc_jmp[local]:
  !p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmtE p (BStmt_Jmp l) st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_valid_pc]
QED


Theorem bir_exec_stmtE_valid_pc_cjmp[local]:
  !p st ex l1 l2.
       bir_is_valid_pc p st.bst_pc ==>
       bir_is_valid_pc p (bir_exec_stmtE p (BStmt_CJmp ex l1 l2) st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
Cases_on `option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val` >- (
  Cases_on `bir_eval_exp ex st.bst_environ` >> (
    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_typeerror_def, LET_DEF]
  )
) >>
rename1 `SOME c` >>
Cases_on `c` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_jmp_valid_pc, LET_DEF]
)
QED


Theorem bir_exec_stmtE_valid_pc_halt[local]:
  !p st ex.  bir_is_valid_pc p st.bst_pc ==>
               bir_is_valid_pc p (bir_exec_stmtE p (BStmt_Halt ex) st).bst_pc
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_halt_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `bir_eval_exp ex st.bst_environ` >> (
    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_typeerror_def, LET_DEF]
  )
QED


Theorem bir_exec_stmtE_valid_pc:
  !p st stmt. bir_is_valid_pc p st.bst_pc ==>
              bir_is_valid_pc p (bir_exec_stmtE p stmt st).bst_pc
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [
    bir_exec_stmtE_valid_pc_cjmp,
    bir_exec_stmtE_valid_pc_jmp,
    bir_exec_stmtE_valid_pc_halt]
)
QED


Theorem bir_exec_stmtE_env_unchanged:
  !p st stmt. (bir_exec_stmtE p stmt st).bst_environ = st.bst_environ
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def,
    bir_exec_stmt_halt_def, bir_exec_stmt_jmp_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_to_label_def,
    bir_state_set_typeerror_def] >>
  REPEAT CASE_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [LET_DEF] >>
  Cases_on `bir_eval_exp b st.bst_environ` >> (
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    rename1 `bir_dest_bool_val abcde` >> Cases_on `bir_dest_bool_val abcde`
  ) >> (
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    COND_CASES_TAC >>
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  )
)
QED


Theorem bir_exec_stmtE_valid_state_invar:
  !p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtE p stmt st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_stmtE_env_unchanged, bir_exec_stmtE_valid_pc]
QED


Theorem bir_exec_stmtE_block_pc:
  !p st stmt. ~(bir_state_is_terminated (bir_exec_stmtE p stmt st)) ==>
              ((bir_exec_stmtE p stmt st).bst_pc.bpc_index = 0)
Proof
REPEAT GEN_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def,
    bir_exec_stmt_halt_def, bir_exec_stmt_jmp_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_to_label_def,
    bir_state_set_typeerror_def] >>
  REPEAT CASE_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF] >>
  Cases_on `bir_eval_exp b st.bst_environ` >> (
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  ) >> (
    rename1 `bir_dest_bool_val abcde` >> Cases_on `bir_dest_bool_val abcde`
  ) >> (
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  ) >> (
    COND_CASES_TAC >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  )
)
QED


Theorem bir_exec_step_valid_pc:
  !p st. bir_is_valid_pc p (bir_exec_step_state p st).bst_pc <=>
         bir_is_valid_pc p st.bst_pc
Proof
REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC std_ss [bir_exec_step_state_def, bir_exec_step_def]
) >>
EQ_TAC >> REPEAT STRIP_TAC >- (
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_step_invalid_pc_THM, bir_exec_step_state_def] >>
  REV_FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_failed_def]
) >>
IMP_RES_TAC bir_exec_step_state_valid_THM >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, bir_exec_stmtE_valid_pc, LET_DEF]
) >>
rename1 `bir_exec_stmtB_state stmt st` >>
Q.ABBREV_TAC `st' = bir_exec_stmtB_state stmt st` >>
`st'.bst_pc = st.bst_pc` by METIS_TAC[bir_exec_stmtB_pc_unchanged] >>
COND_CASES_TAC >> ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_pc_next_valid]
QED


Theorem bir_exec_step_well_typed_env:
  !p st. bir_is_well_typed_env st.bst_environ ==>
         bir_is_well_typed_env (bir_exec_step_state p st).bst_environ
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def] >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_failed_def]
) >>
DISJ2_TAC >>
rename1 `_ = SOME stmt` >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [GSYM bir_exec_stmt_state_def, bir_exec_stmt_state_REWRS, LET_DEF,
    bir_exec_stmtE_env_unchanged]
) >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_stmtB_well_typed_env]
)
QED


Theorem bir_exec_step_valid_state_invar:
  !p st. bir_is_valid_state p st ==>
         bir_is_valid_state p (bir_exec_step_state p st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_step_well_typed_env, bir_exec_step_valid_pc]
QED


val _ = export_theory();
