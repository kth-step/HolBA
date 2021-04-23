open HolKernel Parse boolLib bossLib;

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

Theorem direct_jump_target_block_direct_jump_targets_block_compute:
  ∀l bl.
    direct_jump_target_block l bl ⇒
    MEM l (direct_jump_targets_block_compute bl)
Proof
SIMP_TAC std_ss [direct_jump_target_block_def] >>
REPEAT STRIP_TAC >- (
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [direct_jump_targets_block_compute_def]
) >- (
  Cases_on ‘l2’ >>
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [direct_jump_targets_block_compute_def]
) >>
Cases_on ‘l1’ >>
ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [direct_jump_targets_block_compute_def]
QED

Definition direct_jump_targets_compute_def:
  direct_jump_targets_compute (BirProgram bls) =
  LIST_BIND bls direct_jump_targets_block_compute
End

Theorem direct_jump_target_direct_jump_targets_compute:
  ∀l p. direct_jump_target l p ⇒
        MEM l (direct_jump_targets_compute p)
Proof
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
SIMP_TAC std_ss [direct_jump_target_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [direct_jump_targets_compute_def, LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
Q.EXISTS_TAC ‘direct_jump_targets_block_compute bl’ >>
STRIP_TAC >- (
  Q.EXISTS_TAC ‘bl’ >>
  ASM_SIMP_TAC std_ss [MEM_EL] >>
  PROVE_TAC [bir_get_program_block_info_by_label_THM, bir_get_current_block_SOME]
) >>

IMP_RES_TAC direct_jump_target_block_direct_jump_targets_block_compute
QED

Definition fresh_label_compute_def:
  fresh_label_compute l p =
  (~(MEM l (bir_labels_of_program p)) ∧
   ~(MEM l (direct_jump_targets_compute p)))
End

Theorem fresh_label_compute_sound:
  ∀l p. fresh_label_compute l p ⇒ fresh_label l p
Proof
SIMP_TAC std_ss [fresh_label_compute_def, fresh_label_def] >>
REPEAT STRIP_TAC >>
PROVE_TAC [direct_jump_target_direct_jump_targets_compute]
QED

Definition resolve_fully_def:
  (resolve_fully p l [] v = resolve_fail p l v) ∧
  (resolve_fully p l ((v, sl) :: xs) v' =
     if fresh_label_compute (BL_Label sl) p then
       OPTION_BIND (resolve p l v sl) (\p'. resolve_fully p' (BL_Label sl) xs v')
     else NONE)
End

Theorem resolve_fully_simulated_termination:
  ∀p l xs v' p'.
    resolve_fully p l xs v' = SOME p' ⇒
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
  ∀p l xs v' p'.
    resolve_fully p l xs v' = SOME p' ⇒
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
  ∀p l xs v' p'.
    resolve_fully p l xs v' = SOME p' ⇒
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
  (resolve_fully_n p ((l, xs, v) :: ys) =
     OPTION_BIND (resolve_fully p l xs v) (\p'. resolve_fully_n p' ys))
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
Cases_on ‘h’ >> Cases_on ‘r’ >> rename1 ‘(l, xs, v)’ >>
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
Cases_on ‘h’ >> Cases_on ‘r’ >> rename1 ‘(l, xs, v)’ >>
SIMP_TAC std_ss [resolve_fully_n_def] >>
PROVE_TAC [resolve_fully_vars, SUBSET_TRANS]
QED

Theorem resolve_fully_n_contract_transfer:
  ∀p ys p' l ls pre post.
    resolve_fully_n p ys = SOME p' ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
PROVE_TAC [resolve_fully_n_simulated_termination,
           resolve_fully_n_vars, contract_transfer]
QED


val _ = export_theory();

