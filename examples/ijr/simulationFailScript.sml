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

Theorem bir_exec_stmsB_assert_cjmp:
  ∀bss os c s os2 m2 s2 os1 m1 s1.
    bir_exec_stmtsB (bss ++ [BStmt_Assert (BExp_Const (Imm1 0w))]) (os, c, s) = (os2, m2, s2) ⇒
    bir_exec_stmtsB bss (os, c, s) = (os1, m1, s1) ⇒
    (s1 = s2 ∧ os1 = os2 ∧ m1 = m2 ∧ bir_state_is_terminated s2) ∨
    (s2.bst_status = BST_AssertionViolated)
Proof
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_exec_stmtsB_APPEND] >>
NTAC 2 STRIP_TAC >>
FULL_SIMP_TAC (list_ss++wordsLib.WORD_ss++holBACore_ss)
              [LET_DEF, bir_exec_stmtsB_def,
               bir_exec_stmtB_def, bir_exec_stmt_assert_def,
               bir_dest_bool_val_def, OPT_CONS_REWRS] >>
Cases_on ‘bir_state_is_terminated s1’ >>
FULL_SIMP_TAC std_ss [] >>
Q.PAT_X_ASSUM ‘_ = s2’ (fn thm => ASM_SIMP_TAC (std_ss++holBACore_ss) [GSYM thm])
QED

Theorem bir_exec_block_assert_jmp:
  ∀p' p l1 bss es e s s2 s1 os2 m2 os1 m1 bl1 bl2.
    bl1 = bir_block_t l1 bss (BStmt_Jmp (BLE_Exp e)) ⇒
    bl2 = assert_block l1 bss es ⇒

    bir_exec_block p' bl2 s = (os2, m2, s2) ⇒
    bir_exec_block p bl1 s = (os1, m1, s1) ⇒
    ((s1 = s2 ∧ os1 = os2 ∧ m1 = m2 ∧ bir_state_is_terminated s2) ∨
    (s2.bst_status = BST_AssertionViolated))
Proof
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
rename1 ‘bir_exec_block p' _ _ = (os2', m2', s2'')’ >>
rename1 ‘bir_exec_block p _ _ = (os1', m1', s1'')’ >>

ASM_SIMP_TAC  (std_ss++holBACore_ss) [assert_block_def, bir_exec_block_def] >>
‘∃os2 m2 s2. bir_exec_stmtsB (bss ⧺ [BStmt_Assert (BExp_Const (Imm1 0w))])
                             ([],0,s) = (os2, m2, s2)’
  by PROVE_TAC [pairTheory.PAIR] >>
‘∃os1 m1 s1. bir_exec_stmtsB bss ([],0,s) = (os1, m1, s1)’
  by PROVE_TAC [pairTheory.PAIR] >>
Q.ABBREV_TAC ‘s2' = bir_exec_stmtE p' es s2’ >>
Q.ABBREV_TAC ‘s1' = bir_exec_stmtE p (BStmt_Jmp (BLE_Exp e)) s1’ >>
FULL_SIMP_TAC std_ss [LET_DEF] >>

subgoal ‘(s1 = s2 ∧ os1 = os2 ∧ m1 = m2 ∧ bir_state_is_terminated s2) ∨
         (s2.bst_status = BST_AssertionViolated)’ >- (
  PROVE_TAC [bir_exec_stmsB_assert_cjmp]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
REPEAT STRIP_TAC >- (
  NTAC 6 (POP_ASSUM (fn thm => SIMP_TAC std_ss [GSYM thm])) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
) >>
NTAC 4 (POP_ASSUM (fn thm => SIMP_TAC std_ss [GSYM thm])) >>
FULL_SIMP_TAC  (std_ss++holBACore_ss) []
QED

Theorem resolved_fail_simulated_fail:
  ∀l1 p p'.
    resolved_fail l1 p p' ⇒
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
    PROVE_TAC [resolved_fail_cases]
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
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [resolved_fail_cases]
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
   resolved_fail_block l1 bl1 bl2’ by (
  FULL_SIMP_TAC std_ss [resolved_fail_cases]
) >>
FULL_SIMP_TAC std_ss [resolved_fail_block_cases] >>

IMP_RES_TAC bir_exec_to_labels_block >>
NTAC 2 (Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm])) >>
Q.ABBREV_TAC ‘pc_cond = (F, (λpc. pc.bpc_index = 0 ∧ MEM pc.bpc_label ls))’ >>
‘∃os2 m2 s2. bir_exec_block p' bl2 s = (os2, m2, s2)’ by PROVE_TAC [pairTheory.PAIR] >>
‘∃os1 m1 s1. bir_exec_block p bl1 s = (os1, m1, s1)’ by PROVE_TAC [pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [LET_DEF] >>

subgoal ‘(s1 = s2 ∧ os1 = os2 ∧ m1 = m2 ∧ bir_state_is_terminated s2) ∨
         (s2.bst_status = BST_AssertionViolated)’ >- (
  PROVE_TAC [bir_exec_block_assert_jmp]
) >- (
  FULL_SIMP_TAC (list_ss++holBACore_ss) [bir_exec_to_labels_def,
                                         bir_exec_to_labels_n_REWR_TERMINATED]
) >>
Q.UNABBREV_TAC ‘pc_cond’ >>
FULL_SIMP_TAC (list_ss++holBACore_ss) [Once bir_state_COUNT_PC_def,
                                       bir_exec_to_labels_def,
                                       bir_exec_to_labels_n_REWR_TERMINATED] >>

PROVE_TAC []
QED


val _ = export_theory();

