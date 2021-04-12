open HolKernel Parse boolLib bossLib;

open listTheory pred_setSimps;

open bir_programTheory bir_expTheory bir_exp_immTheory bir_typing_expTheory;
open bir_valuesTheory bir_auxiliaryTheory
open bir_program_blocksTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;

open resolutionTheory simulationTheory;

val _ = new_theory "simulationFail";


Definition simulated_fail_def:
  simulated_fail (p: 'a bir_program_t) (p': 'a bir_program_t) =
  ∀s l s' o2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒

    exec_to_prog p' s p = BER_Ended o2 m2 n2 s' ⇒
    ~(s'.bst_status = BST_AssertionViolated) ⇒
    (∃o1 m1 n1.
      exec_to_prog p s p = BER_Ended o1 m1 n1 s')
End

Theorem bir_exec_block_assert:
  ∀p l v s bl.
    ~(bir_state_is_terminated s) ⇒
    bl = bir_block_t l [BStmt_Assert (BExp_Const (Imm1 0w))] (BStmt_Halt v) ⇒
    (∃s'. bir_exec_block p bl s = ([], 1, s') ∧
          s'.bst_status = BST_AssertionViolated)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss++wordsLib.WORD_ss++holBACore_ss)
              [bir_exec_block_def, bir_exec_stmtsB_def,
               bir_exec_stmtB_def, bir_exec_stmt_assert_def,
               bir_dest_bool_val_def, LET_DEF, OPT_CONS_REWRS]
QED

Theorem bir_exec_to_labels_assert:
  ∀l v ls p s bl.
    ~(bir_state_is_terminated s) ⇒
    bl = bir_block_t l [BStmt_Assert (BExp_Const (Imm1 0w))] (BStmt_Halt v) ⇒
    bir_get_current_block p (s.bst_pc) = SOME bl ⇒
    (∃s'. bir_exec_to_labels ls p s = BER_Ended [] 1 0 s' ∧
            s'.bst_status = BST_AssertionViolated)
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_to_labels_block >>
Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm]) >>
IMP_RES_TAC bir_exec_block_assert >>
Q.PAT_X_ASSUM `∀p. _` (fn thm => ASSUME_TAC (Q.SPEC `p` thm)) >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
FULL_SIMP_TAC  (list_ss++holBACore_ss) [LET_DEF, bir_state_COUNT_PC_def,
                                        bir_exec_to_labels_def,
                                        bir_exec_to_labels_n_REWR_TERMINATED]
QED

Theorem resolved_fail_simulated_fail:
  ∀l1 v p p'.
    resolved_fail l1 v p p' ⇒
    simulated_fail p p'
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
SIMP_TAC std_ss [simulated_fail_def, exec_to_prog_def] >>
Q.ABBREV_TAC ‘ls = (bir_labels_of_program p)’ >>
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
rename1 ‘_ = BER_Ended o2' m2' n2' s''’ >>

(*Same block*)
REVERSE (Cases_on ‘l = l1’) >- (
  ‘∃bl. bir_get_current_block p s.bst_pc = SOME bl ∧
        bir_get_current_block p' s.bst_pc = SOME bl’ by (
    PROVE_TAC [resolved_fail_def_cases]
  ) >>

  IMP_RES_TAC bir_exec_to_labels_block >>
  NTAC 2 (Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm])) >>
  Q.ABBREV_TAC ‘pc_cond = (F, (λpc. pc.bpc_index = 0 ∧ MEM pc.bpc_label ls))’ >>
  ‘∃os2 m2 s2. bir_exec_block p' bl s = (os2, m2, s2)’ by PROVE_TAC [pairTheory.PAIR] >>
  ‘∃os1 m1 s1. bir_exec_block p bl s = (os1, m1, s1)’ by PROVE_TAC [pairTheory.PAIR] >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>

  (*Programs execute block bl with same result*)
  Q.SUBGOAL_THEN ‘s2 = s1 ∧ os2 = os1 ∧ m2 = m1’ (fn thm => SIMP_TAC std_ss [thm]) >- (
    MP_TAC (Q.SPECL [‘p'’, ‘p’, ‘{}’, ‘bl’, ‘s’, ‘s2’, ‘os2’, ‘m2’] bir_exec_block_same) >>
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [resolved_fail_def_cases]
  ) >>

  (*Programs fail*)
  REVERSE (Cases_on ‘s1.bst_status = BST_Running’) >- (
    ‘bir_state_is_terminated s1’ by ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
    FULL_SIMP_TAC (std_ss++bir_TYPES_ss)
                  [bir_exec_to_labels_def, bir_exec_to_labels_n_REWR_TERMINATED]
  ) >>

  (*Programs successfully jump*)
  ‘0 < m1 ∧ bir_state_COUNT_PC pc_cond s1’ by (
    METIS_TAC [resolved_simulated_lem]
  ) >> ASM_SIMP_TAC (std_ss++holBACore_ss) []
) >>

(*Different blocks*)
POP_ASSUM SUBST_ALL_TAC >>
‘∃bl1 bl2.
   bir_get_current_block p s.bst_pc = SOME bl1 ∧
   bir_get_current_block p' s.bst_pc = SOME bl2 ∧
   resolved_fail_block l1 v bl1 bl2’ by (
  FULL_SIMP_TAC std_ss [resolved_fail_def_cases]
) >>
FULL_SIMP_TAC std_ss [resolved_fail_block_def_cases] >>

Cases_on ‘bir_state_is_terminated s’ >- (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss)
                  [bir_exec_to_labels_def, bir_exec_to_labels_n_REWR_TERMINATED]
) >>
IMP_RES_TAC bir_exec_to_labels_assert >>
POP_ASSUM (fn thm => ASSUME_TAC (Q.SPEC ‘set ls’ thm)) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED


val _ = export_theory();

