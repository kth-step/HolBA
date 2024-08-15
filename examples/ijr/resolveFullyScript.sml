open HolKernel Parse boolLib bossLib BasicProvers;

open listTheory optionTheory pred_setTheory pred_setSimps;

open bir_programTheory bir_program_blocksTheory;
open HolBACoreSimps;

open resolutionTheory resolveTheory contractTransferTheory;

val _ = new_theory "resolveFully";


Definition direct_jump_targets_block_compute_def:
  direct_jump_targets_block_compute bl =
  case bl.bb_last_statement of
    BStmt_Jmp (BLE_Label l) => [l]
  | BStmt_CJmp e (BLE_Label l1) (BLE_Label l2) => [l1; l2]
  | BStmt_CJmp e (BLE_Label l1) _ => [l1]
  | BStmt_CJmp e  _ (BLE_Label l2) => [l2]
  | _ => []
End

Definition fresh_label_compute_def:
  (fresh_label_compute l (BirProgram []) = T) ∧
  (fresh_label_compute l (BirProgram (bl::bls)) =
    (~(bl.bb_label = l) ∧
     ~(MEM l (direct_jump_targets_block_compute bl)) ∧
     fresh_label_compute l (BirProgram bls)))
End

Theorem fresh_label_compute_sound:
  ∀l p. fresh_label_compute l p ⇒ fresh_label l p
Proof
Cases_on ‘p’ >> rename1 ‘BirProgram bls’ >>
Induct_on ‘bls’ >- (
  SIMP_TAC list_ss [fresh_label_def, bir_labels_of_program_def,
                    direct_jump_target_def, bir_get_current_block_def,
                    bir_get_program_block_info_by_label_def, INDEX_FIND_def]
) >>

SIMP_TAC std_ss [fresh_label_compute_def, fresh_label_def] >>
NTAC 4 STRIP_TAC >>
‘fresh_label l (BirProgram bls)’ by PROVE_TAC [] >- (
  SIMP_TAC list_ss [bir_labels_of_program_def] >>
  PROVE_TAC [bir_labels_of_program_def, fresh_label_def]
) >>

SIMP_TAC std_ss [direct_jump_target_def] >>
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_get_current_block_def,
                                 bir_get_program_block_info_by_label_def,
                                 INDEX_FIND_def, bir_block_pc_def] >>
CASE_TAC >- (
  FULL_SIMP_TAC std_ss [direct_jump_target_block_def,
                        direct_jump_targets_block_compute_def] >>
  DISCH_THEN SUBST_ALL_TAC >>
  EVERY_CASE_TAC >>
  FULL_SIMP_TAC (list_ss++bir_TYPES_ss) []
) >>                          

FULL_SIMP_TAC (list_ss++bir_TYPES_ss) [fresh_label_def, direct_jump_target_def,
                                       bir_get_current_block_def, bir_block_pc_def,
                                       bir_get_program_block_info_by_label_def] >>
SIMP_TAC std_ss [Once holba_auxiliaryTheory.INDEX_FIND_INDEX_CHANGE] >>
Q.PAT_X_ASSUM ‘∀l'' bl. _’ (MP_TAC o Q.SPECL [‘l'’, ‘bl’]) >>
EVERY_CASE_TAC >>
FULL_SIMP_TAC std_ss [] >>
Cases_on ‘x’ >>
FULL_SIMP_TAC std_ss []
QED

Definition resolve_fully_def:
  (resolve_fully p l [] = resolve_fail p l) ∧
  (resolve_fully p l ((v, sl) :: xs) =
     if fresh_label_compute (BL_Label sl) p then
       OPTION_BIND (resolve p l v sl) (\p'. resolve_fully p' (BL_Label sl) xs)
     else NONE)
End

Theorem resolve_fully_simulated_termination:
  ∀p l xs p'.
    resolve_fully p l xs = SOME p' ⇒
    simulated_termination p p'
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >- (
  PROVE_TAC [resolve_fully_def, resolve_fail_simulated_termination]
) >>

rename1 ‘SOME p''’ >>
Cases_on ‘h’ >> rename1 ‘(v, sl)’ >>
SIMP_TAC std_ss [resolve_fully_def] >>
PROVE_TAC [resolve_simulated_termination, fresh_label_compute_sound,
           resolve_labels, simulated_termination_transitive]
QED

Theorem resolve_fully_vars:
  ∀p l xs p'.
    resolve_fully p l xs = SOME p' ⇒
    bir_vars_of_program p' SUBSET bir_vars_of_program p
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >- (
  PROVE_TAC [resolve_fully_def, resolve_fail_vars]
) >>

rename1 ‘SOME p''’ >>
Cases_on ‘h’ >> rename1 ‘(v, sl)’ >>
SIMP_TAC std_ss [resolve_fully_def] >>
PROVE_TAC [resolve_vars, SUBSET_TRANS]
QED

Theorem resolve_fully_labels:
  ∀p l xs p'.
    resolve_fully p l xs = SOME p' ⇒
    set (bir_labels_of_program p) SUBSET set (bir_labels_of_program p')
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >- (
  PROVE_TAC [resolve_fully_def, resolve_fail_labels, SUBSET_REFL]
) >>

rename1 ‘SOME p''’ >>
Cases_on ‘h’ >> rename1 ‘(v, sl)’ >>
SIMP_TAC std_ss [resolve_fully_def] >>
PROVE_TAC [resolve_labels, SUBSET_TRANS]
QED

Definition resolve_fully_n_def:
  (resolve_fully_n p [] = SOME p) ∧
  (resolve_fully_n p ((l, xs) :: ys) =
     OPTION_BIND (resolve_fully p l xs) (\p'. resolve_fully_n p' ys))
End

Theorem resolve_fully_n_simulated_termination:
  ∀p ys p'.
    resolve_fully_n p ys = SOME p' ⇒
    simulated_termination p p'
Proof
Induct_on ‘ys’ >>
REPEAT GEN_TAC >- (
  SIMP_TAC std_ss [resolve_fully_n_def, simulated_termination_REFL]
) >>

rename1 ‘SOME p''’ >>
Cases_on ‘h’ >> Cases_on ‘r’ >> rename1 ‘(l, xs)’ >>
SIMP_TAC std_ss [resolve_fully_n_def] >>
PROVE_TAC [resolve_fully_simulated_termination,
           resolve_fully_labels, simulated_termination_transitive]
QED

Theorem resolve_fully_n_vars:
  ∀p ys p'.
    resolve_fully_n p ys = SOME p' ⇒
    bir_vars_of_program p' SUBSET bir_vars_of_program p
Proof
Induct_on ‘ys’ >>
REPEAT GEN_TAC >- (
  SIMP_TAC std_ss [resolve_fully_n_def, SUBSET_REFL]
) >>

rename1 ‘SOME p''’ >>
Cases_on ‘h’ >> Cases_on ‘r’ >> rename1 ‘(l, xs)’ >>
SIMP_TAC std_ss [resolve_fully_n_def] >>
PROVE_TAC [resolve_fully_vars, SUBSET_TRANS]
QED

Theorem resolve_fully_n_bir_exec_to_labels_triple_transfer:
  ∀p ys p' l ls pre post.
    resolve_fully_n p ys = SOME p' ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
PROVE_TAC [resolve_fully_n_simulated_termination,
           resolve_fully_n_vars, bir_exec_to_labels_triple_transfer]
QED

Theorem resolve_fully_n_contract_transfer:
  ∀p ys p' i l ls ls' pre post.
    resolve_fully_n p ys = SOME p' ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒
    ls' SUBSET (set (bir_labels_of_program p)) ⇒

    bir_simp_jgmt p' i l ls ls' pre post ⇒
    bir_simp_jgmt p i l ls ls' pre post                         
Proof
PROVE_TAC [resolve_fully_n_simulated_termination,
           resolve_fully_n_vars, contract_transfer]
QED


val _ = export_theory();

