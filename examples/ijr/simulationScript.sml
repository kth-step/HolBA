open HolKernel Parse boolLib bossLib;

open listTheory;

open bir_programTheory bir_expTheory bir_exp_immTheory bir_typing_expTheory;
open bir_program_blocksTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;

open resolutionTheory;

val _ = new_theory "simulation";


Definition exec_to_prog_def:
  exec_to_prog p s pls =
  bir_exec_to_labels (set (bir_labels_of_program pls)) p s
End

Definition simulated_def:
  simulated (p: 'a bir_program_t) (p': 'a bir_program_t) =
  ∀s l s' o2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒

    exec_to_prog p' s p = BER_Ended o2 m2 n2 s' ⇒
    ~(∃l'. s'.bst_status = BST_JumpOutside l') ⇒
    (∃o1 m1 n1.
      exec_to_prog p s p = BER_Ended o1 m1 n1 s')
End


Theorem bir_exec_stmt_jmp_to_label_same:
  ∀l p' p s s'.
    (MEM l (bir_labels_of_program p') ⇔ MEM l (bir_labels_of_program p)) ⇒
    bir_exec_stmt_jmp_to_label p' l s = s' ⇒
    bir_exec_stmt_jmp_to_label p l s = s'
Proof
SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def]
QED

Theorem bir_eval_label_exp_lem:
  ∀p' p sl le s l.
    (∀l'. MEM l' (bir_labels_of_program p') ⇔
            MEM l' (bir_labels_of_program p) ∨ l' = (BL_Label sl)) ⇒
    le ≠ BLE_Label (BL_Label sl) ⇒
    bir_eval_label_exp le s.bst_environ = SOME l ⇒
    (MEM l (bir_labels_of_program p') ⇔ MEM l (bir_labels_of_program p))
Proof
REPEAT STRIP_TAC >>
Cases_on ‘le’ >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_label_exp_def]
) >>
rename1 ‘BLE_Exp e’ >>
FULL_SIMP_TAC std_ss [bir_eval_label_exp_def] >>
Cases_on ‘bir_eval_exp e s.bst_environ’ >- (
  FULL_SIMP_TAC std_ss []
) >> FULL_SIMP_TAC std_ss [] >>
rename1 ‘_ = SOME v’ >>
Cases_on ‘v’ >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  RW_TAC (std_ss++holBACore_ss) []
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem bir_exec_stmt_jmp_same:
  ∀p' p sl le s s'.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    le ≠ BLE_Label (BL_Label sl) ⇒
    bir_exec_stmt_jmp p' le s = s' ⇒
    bir_exec_stmt_jmp p le s = s'
Proof
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>

(*le not well typed*)
Cases_on ‘bir_eval_label_exp le s.bst_environ’ >- (
  ASM_SIMP_TAC std_ss []
) >> ASM_SIMP_TAC std_ss [] >>

(*le well typed*)
rename1 ‘_ = SOME l’ >>
subgoal ‘MEM l (bir_labels_of_program p') ⇔ MEM l (bir_labels_of_program p)’ >- (
  IMP_RES_TAC bir_eval_label_exp_lem
) >>
PROVE_TAC [bir_exec_stmt_jmp_to_label_same]
QED

Theorem bir_exec_stmt_cjmp_same:
  ∀p' p sl le1 le2 c s s' .
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    le1 ≠ BLE_Label (BL_Label sl) ⇒
    le2 ≠ BLE_Label (BL_Label sl) ⇒
    bir_exec_stmt_cjmp p' c le1 le2 s = s' ⇒
    bir_exec_stmt_cjmp p c le1 le2 s = s'
Proof
RW_TAC std_ss [bir_exec_stmt_cjmp_def] >>

(*c not well typed*)
Cases_on ‘vobc’ >- (
  ASM_SIMP_TAC std_ss []
) >> ASM_SIMP_TAC std_ss [] >>

(*c well typed*)
METIS_TAC [bir_exec_stmt_jmp_same]
QED

Theorem bir_exec_block_same:
  ∀p' p sl bl s s' os m.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    ~(direct_jump_target_block (BL_Label sl) bl) ⇒
    bir_exec_block p' bl s = (os, m, s') ⇒
    bir_exec_block p bl s = (os, m, s')
Proof
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
rename1 ‘_ = (os', m', s'')’ >>

(*Execution of basic statements has same result*)
SIMP_TAC std_ss [bir_exec_block_def] >>
‘∃os m s'. bir_exec_stmtsB bl.bb_statements ([], 0, s) = (os, m, s')’ by
  PROVE_TAC [pairTheory.PAIR] >>
Q.ABBREV_TAC ‘s2 = bir_exec_stmtE p' bl.bb_last_statement s'’ >>
Q.ABBREV_TAC ‘s1 = bir_exec_stmtE p bl.bb_last_statement s'’ >>
FULL_SIMP_TAC std_ss [LET_DEF] >>

(*Already terminated after execution of basic statements*)
Cases_on ‘bir_state_is_terminated s'’ >- (
  ASM_SIMP_TAC std_ss []
) >> ASM_SIMP_TAC std_ss [] >>

(*Still running after execution of basic statements*)

(*Last statement is Jmp*)
Cases_on ‘bl.bb_last_statement’ >>
FULL_SIMP_TAC std_ss [bir_exec_stmtE_def] >- (
  rename1 ‘_ = BStmt_Jmp le’ >>
  ‘le ≠ BLE_Label (BL_Label sl)’ by (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [direct_jump_target_block_def]
  ) >>
  METIS_TAC [bir_exec_stmt_jmp_same]
) >>

(*Last statement is CJmp*)
rename1 ‘_ = BStmt_CJmp c le1 le2’ >>
subgoal ‘le1 ≠ BLE_Label (BL_Label sl) ∧
         le2 ≠ BLE_Label (BL_Label sl)’ >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [direct_jump_target_block_def] >>
  PROVE_TAC []
) >>
METIS_TAC [bir_exec_stmt_cjmp_same]
QED


(*TODO: Simplify long theorem propositions?*)

Definition jump_fresh_def:
  jump_fresh e s s2 sl s1 p =
  ∃v.
  (bir_eval_exp e s.bst_environ = SOME (BVal_Imm v) ∧
   s.bst_status = BST_Running ∧
   s2 = s with bst_pc := bir_block_pc (BL_Label sl) ∧
   (MEM (BL_Address v) (bir_labels_of_program p) ⇒
    s1 = s with bst_pc := bir_block_pc (BL_Address v)))
End

Theorem jump_fresh_terminated:
  ∀e s s2 sl s1 p.
    ~(bir_state_is_terminated s) ⇒
    jump_fresh e s s2 sl s1 p ⇒
    ~(bir_state_is_terminated s2)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [jump_fresh_def, bir_state_is_terminated_def] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
QED

Theorem bir_exec_stmtE_cjmp_jmp:
  ∀p' p sl es1 e c v es2 s s2 s1.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    MEM (BL_Address v) (bir_labels_of_program p) ⇒
    type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v)) ⇒

    es1 = BStmt_Jmp (BLE_Exp e) ⇒
    c = BExp_BinPred BIExp_Equal e (BExp_Const v) ⇒
    es2 = BStmt_CJmp c (BLE_Label (BL_Address v)) (BLE_Label (BL_Label sl)) ⇒

    s.bst_status = BST_Running ⇒
    bir_exec_stmtE p' es2 s = s2 ⇒
    bir_exec_stmtE p es1 s = s1 ⇒
    (s1 = s2 ∨ jump_fresh e s s2 sl s1 p)
Proof
REPEAT GEN_TAC >> NTAC 3 STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def, LET_DEF] >>
NTAC 3 (DISCH_THEN (K ALL_TAC)) >>
rename1 ‘MEM (BL_Address v') _’ >>

(*e not well typed*)
Cases_on ‘bir_eval_exp e s.bst_environ’ >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def, bir_eval_label_exp_def]
) >>
REVERSE (Cases_on ‘x’) >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def, bir_eval_label_exp_def]
) >>

(*e well typed*)
ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 ‘_ = SOME (BVal_Imm v)’ >>

(*e and v must have same type*)
Q.SUBGOAL_THEN ‘type_of_bir_imm v = type_of_bir_imm v'’
 (fn thm => SIMP_TAC (std_ss++holBACore_ss) [thm]) >- (
  MP_TAC (Q.SPECL [‘s.bst_environ’, ‘e’, ‘BType_Imm (type_of_bir_imm v')’] type_of_bir_exp_THM) >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []
) >>

(*e = v*)
Cases_on ‘bir_bin_pred BIExp_Equal v v'’ >>
ASM_SIMP_TAC std_ss [] >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_bin_pred_Equal_REWR, bir_exec_stmt_jmp_def,
     bir_eval_label_exp_def] >>
  PROVE_TAC [bir_exec_stmt_jmp_to_label_same]
) >>

(*e ≠ v*)
FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_bin_pred_Equal_REWR, bir_exec_stmt_jmp_def,
     bir_eval_label_exp_def, bir_exec_stmt_jmp_to_label_def] >>
PROVE_TAC [jump_fresh_def]
QED

Definition exec_stmtsB_def:
  exec_stmtsB bss s =
  let (os, m, s') = bir_exec_stmtsB bss ([],0,s) in
  s'
End

(*TODO: Last case in bir_exec_block_cjmp_jmp and resolved_simulated chaosy *)

Theorem bir_exec_block_cjmp_jmp:
  ∀p' p sl  bl1 l1 bss e c v bl2 s s2 os2 m2 s1 os1 m1.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    ~(direct_jump_target_block (BL_Label sl) bl1) ⇒
    MEM (BL_Address v) (bir_labels_of_program p) ⇒
    type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v)) ⇒

    bl1 = bir_block_t l1 bss (BStmt_Jmp (BLE_Exp e)) ⇒
    c = BExp_BinPred BIExp_Equal e (BExp_Const v) ⇒
    bl2 = bir_block_t l1 bss
      (BStmt_CJmp c (BLE_Label (BL_Address v)) (BLE_Label (BL_Label sl))) ⇒

    bir_exec_block p' bl2 s = (os2, m2, s2) ⇒
    bir_exec_block p bl1 s = (os1, m1, s1) ⇒
    (s1 = s2 ∧ os1 = os2 ∧ m1 = m2) ∨ (jump_fresh e (exec_stmtsB bss s) s2 sl s1 p)
Proof
REPEAT GEN_TAC >> NTAC 4 STRIP_TAC >>
rename1 ‘bir_exec_block p' _  _= (os2', m2', s2')’ >>
rename1 ‘bir_exec_block p _ _ = (os1', m1', s1')’ >>

(*Execution of basic statements has same result*)
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_block_def] >>
NTAC 3 (DISCH_THEN (K ALL_TAC)) >>
‘∃os m s'. bir_exec_stmtsB bss ([], 0, s) = (os, m, s')’ by
  PROVE_TAC [pairTheory.PAIR] >>
Q.ABBREV_TAC ‘c = BExp_BinPred BIExp_Equal e (BExp_Const v)’ >>

Q.ABBREV_TAC ‘s2 = bir_exec_stmtE p'
  (BStmt_CJmp c (BLE_Label (BL_Address v)) (BLE_Label (BL_Label sl))) s'’ >>
Q.ABBREV_TAC ‘s1 = bir_exec_stmtE p (BStmt_Jmp (BLE_Exp e)) s'’ >>
FULL_SIMP_TAC std_ss [LET_DEF] >>

(*Already terminated after execution of basic statements*)
Cases_on ‘bir_state_is_terminated s'’ >- (
  ASM_SIMP_TAC std_ss []
) >> ASM_SIMP_TAC std_ss [] >>

(*Still running after execution of basic statements*)
‘s'.bst_status = BST_Running’ by FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def] >>
(*e = v*)
‘s2 = s1 ∨ jump_fresh e s' s2 sl s1 p’ by METIS_TAC [bir_exec_stmtE_cjmp_jmp] >- (
  ASM_SIMP_TAC std_ss []
) >>

(*e ≠ v*)
IMP_RES_TAC jump_fresh_terminated >>
POP_ASSUM (fn thm => SIMP_TAC std_ss [thm]) >>
FULL_SIMP_TAC std_ss [jump_fresh_def] >>
Cases_on ‘MEM (BL_Address v') (bir_labels_of_program p)’ >>
FULL_SIMP_TAC std_ss [] >- (
  subgoal ‘~(bir_state_is_terminated s1)’ >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
  ) >> REV_FULL_SIMP_TAC std_ss [] >>
  REPEAT STRIP_TAC >> DISJ2_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [jump_fresh_def, exec_stmtsB_def, LET_DEF]
) >>

REPEAT STRIP_TAC >> DISJ2_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [jump_fresh_def, exec_stmtsB_def, LET_DEF]
QED


Theorem bir_exec_block_jmp:
  ∀p' p sl s e v bl.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    ~(bir_state_is_terminated s) ⇒
    bir_eval_exp e s.bst_environ = SOME (BVal_Imm v) ⇒
    bl = bir_block_t (BL_Label sl) [] (BStmt_Jmp (BLE_Exp e)) ⇒
    (∃s'. bir_exec_block p' bl s = ([], 1, s') ∧
          if MEM (BL_Address v) (bir_labels_of_program p) then
            s' = s with bst_pc := bir_block_pc (BL_Address v)
          else s'.bst_status = BST_JumpOutside (BL_Address v))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss++holBACore_ss)
              [bir_exec_block_def, bir_exec_stmtsB_def, LET_DEF,
               bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_eval_label_exp_def,
               bir_exec_stmt_jmp_to_label_def, bir_state_is_terminated_def]
QED

Theorem bir_exec_to_labels_jmp:
  ∀(p' : 'a bir_program_t) (p : 'a bir_program_t) sl e s v bl ls.
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ⇒
    ~(bir_state_is_terminated s) ⇒
    bir_eval_exp e s.bst_environ = SOME (BVal_Imm v) ⇒

    bl = bir_block_t (BL_Label sl) [] (BStmt_Jmp (BLE_Exp e)) ⇒
    bir_get_current_block p' (s.bst_pc) = SOME bl ⇒
    ls = bir_labels_of_program p ⇒
    (∃s' n. bir_exec_to_labels (set ls) p' s = BER_Ended [] 1 n s' ∧
            if MEM (BL_Address v) (bir_labels_of_program p) then
              s' = s with bst_pc := bir_block_pc (BL_Address v)
            else s'.bst_status = BST_JumpOutside (BL_Address v))
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_to_labels_block >>
Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm]) >>
IMP_RES_TAC bir_exec_block_jmp >>
Cases_on ‘MEM (BL_Address v) (bir_labels_of_program p)’ >>
FULL_SIMP_TAC (list_ss++holBACore_ss)
              [LET_DEF, bir_state_COUNT_PC_def, bir_state_is_terminated_def,
               bir_block_pc_def] >>

(*v not in labels of p*)
FULL_SIMP_TAC  (std_ss++holBACore_ss)
               [bir_exec_to_labels_def, bir_exec_to_labels_n_REWR_TERMINATED,
                bir_block_pc_def]
QED


Theorem resolved_simulated_lem:
  ∀p s bl os m s' pc_cond ls.
    bir_get_current_block p s.bst_pc = SOME bl ⇒
    bir_exec_block p bl s = (os, m, s') ⇒
    s'.bst_status = BST_Running ⇒
    ls = bir_labels_of_program p ⇒
    pc_cond = (F, (λpc. pc.bpc_index = 0 ∧ MEM pc.bpc_label ls)) ⇒
    0 < m ∧ bir_state_COUNT_PC pc_cond s'
Proof
REPEAT STRIP_TAC >>
‘~(bir_state_is_terminated s')’ by ASM_SIMP_TAC (std_ss++holBACore_ss) [] >- (
  CCONTR_TAC >>
  ‘m = 0’ by DECIDE_TAC >>
  PROVE_TAC [bir_exec_block_REWR_NO_STEP]
) >>

ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_COUNT_PC_def] >>
‘IS_SOME (bir_get_current_block p s'.bst_pc)’ by PROVE_TAC [bir_exec_block_new_block_pc] >>
‘∃l. s'.bst_pc = bir_block_pc l’ by (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_block_pc_def, bir_get_current_block_def,
                                        optionTheory.IS_SOME_EXISTS,
                                        bir_programcounter_t_component_equality]
) >> POP_ASSUM SUBST_ALL_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_block_pc_def, bir_get_current_block_block_pc_IS_SOME]
QED


val quantifiers = [‘p'’, ‘p’, ‘sl’, ‘bl1’, ‘l1’, ‘bss’, ‘e’, ‘c’, ‘v’,
                   ‘bl2’, ‘s’, ‘s2’, ‘os2’, ‘m2’, ‘s1’, ‘os1’, ‘m1’]


(*TODO: simplify repetitiveness in cases?*)
Theorem resolved_simulated:
  ∀l1 v sl p p'.
    resolved l1 v sl p p' ⇒
    simulated p p'
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
SIMP_TAC std_ss [simulated_def, exec_to_prog_def] >>
Q.ABBREV_TAC ‘ls = (bir_labels_of_program p)’ >>
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
rename1 ‘_ = BER_Ended o2' m2' n2' s''’ >>

(*Same block*)
REVERSE (Cases_on ‘l = l1’) >- (
  ‘∃bl. bir_get_current_block p s.bst_pc = SOME bl ∧
        bir_get_current_block p' s.bst_pc = SOME bl’ by (
    PROVE_TAC [resolved_def_cases]
  ) >>

  IMP_RES_TAC bir_exec_to_labels_block >>
  NTAC 2 (Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm])) >>
  Q.ABBREV_TAC ‘pc_cond = (F, (λpc. pc.bpc_index = 0 ∧ MEM pc.bpc_label ls))’ >>
  ‘∃os2 m2 s2. bir_exec_block p' bl s = (os2, m2, s2)’ by PROVE_TAC [pairTheory.PAIR] >>
  ‘∃os1 m1 s1. bir_exec_block p bl s = (os1, m1, s1)’ by PROVE_TAC [pairTheory.PAIR] >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>

  (*Programs execute block bl with same result*)
  Q.SUBGOAL_THEN ‘s2 = s1 ∧ os2 = os1 ∧ m2 = m1’ (fn thm => SIMP_TAC std_ss [thm]) >- (
    MP_TAC (Q.SPECL [‘p'’, ‘p’, ‘sl’, ‘bl’, ‘s’, ‘s2’, ‘os2’, ‘m2’] bir_exec_block_same) >>
    FULL_SIMP_TAC std_ss [resolved_def_cases, fresh_label_def, direct_jump_target_def]
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
‘∃bl1 bl2 bl3.
   bir_get_current_block p s.bst_pc = SOME bl1 ∧
   bir_get_current_block p' s.bst_pc = SOME bl2 ∧
   bir_get_current_block p' (bir_block_pc (BL_Label sl)) = SOME bl3 ∧
   resolved_block l1 v sl bl1 bl2 bl3’ by (
  FULL_SIMP_TAC std_ss [resolved_def_cases]
) >>
FULL_SIMP_TAC std_ss [resolved_block_def_cases] >>
Q.ABBREV_TAC ‘c = BExp_BinPred BIExp_Equal e (BExp_Const v)’ >>

IMP_RES_TAC bir_exec_to_labels_block >>
NTAC 2 (Q.PAT_X_ASSUM `∀ls. _` (fn thm => SIMP_TAC std_ss [Q.SPEC `ls` thm])) >>
Q.ABBREV_TAC ‘pc_cond = (F, (λpc. pc.bpc_index = 0 ∧ MEM pc.bpc_label ls))’ >>
‘∃os2 m2 s2. bir_exec_block p' bl2 s = (os2, m2, s2)’ by PROVE_TAC [pairTheory.PAIR] >>
‘∃os1 m1 s1. bir_exec_block p bl1 s = (os1, m1, s1)’ by PROVE_TAC [pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [LET_DEF] >>

(*e = v*)
subgoal ‘(s1 = s2 ∧ os1 = os2 ∧ m1 = m2) ∨
         jump_fresh e (exec_stmtsB bss s) s2 sl s1 p’ >- (
    MP_TAC (Q.SPECL quantifiers bir_exec_block_cjmp_jmp) >>
    FULL_SIMP_TAC std_ss [resolved_def_cases, fresh_label_def,
                          direct_jump_target_def, resolved_block_def_cases]
) >- (
  (*Programs execute block labelled l1 with same result*)
  NTAC 3 (POP_ASSUM (fn thm => SIMP_TAC std_ss [GSYM thm])) >>

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

(*e ≠ v*)
(*Programs execute block l1 with different results:
  p tries to jump to e, p' jumps to sl*)
FULL_SIMP_TAC std_ss [jump_fresh_def] >>
Q.PAT_ASSUM ‘s2 = _’ (fn thm => SIMP_TAC std_ss [GSYM thm]) >>

(*Program p' continues execution*)
Q.SUBGOAL_THEN ‘~(bir_state_COUNT_PC pc_cond s2)’ (fn thm => SIMP_TAC std_ss [thm]) >- (
  Q.UNABBREV_TAC ‘pc_cond’ >>
  FULL_SIMP_TAC  (std_ss++holBACore_ss)
                 [bir_state_COUNT_PC_def, jump_fresh_def,
                 bir_block_pc_def, resolved_def_cases, fresh_label_def]
) >>

(*Program p' executes block sl and tries to jump to e*)
subgoal ‘∃s2' n. bir_exec_to_labels (set ls) p' s2 = BER_Ended [] 1 n s2' ∧
                 if MEM (BL_Address v') (bir_labels_of_program p) then
                   s2' = s2 with bst_pc := bir_block_pc (BL_Address v')
                 else s2'.bst_status = BST_JumpOutside (BL_Address v')’ >- (
  MP_TAC (Q.SPECL [‘p'’, ‘p’, ‘sl’, ‘e’, ‘s2’, ‘v'’] bir_exec_to_labels_jmp) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [resolved_def_cases]
) >>

(*Evaluation of e in labels of p*)
Cases_on ‘MEM (BL_Address v') (bir_labels_of_program p)’ >>
FULL_SIMP_TAC (list_ss++holBACore_ss) []  >- (
  (*Programs successfully jump to e*)
  STRIP_TAC >> POP_ASSUM (fn thm => ASSUME_TAC (GSYM thm)) >>
  subgoal ‘0 < m1 ∧ bir_state_COUNT_PC pc_cond s1’ >- (
    MP_TAC (Q.SPECL [‘p’, ‘s’, ‘bl1’, ‘os1’, ‘m1’, ‘s1’] resolved_simulated_lem) >>
    ASM_SIMP_TAC  (std_ss++holBACore_ss) []
  ) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>

(*Evaluation of e not in labels of p*)
(*Programs jumps outside to e*)
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss++holBACore_ss) []
QED


val _ = export_theory();

