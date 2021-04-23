open HolKernel Parse boolLib bossLib;

open listTheory pred_setTheory pred_setSimps;

open bir_programTheory bir_expTheory bir_exp_immTheory bir_typing_progTheory;
open bir_program_blocksTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;

val _ = new_theory "resolution";

Definition cjmp_stmtE_def:
  cjmp_stmtE e v sl =
   BStmt_CJmp (BExp_BinPred BIExp_Equal e (BExp_Const v))
              (BLE_Label (BL_Address v))
              (BLE_Label (BL_Label sl))
End

Definition cjmp_block_def:
  cjmp_block l1 bss e v sl =
  <| bb_label :=  l1;
     bb_statements := bss;
     bb_last_statement := cjmp_stmtE e v sl |>
End

Definition jmp_block_def:
  jmp_block sl e =
  <| bb_label := BL_Label sl;
     bb_statements := [];
     bb_last_statement := BStmt_Jmp (BLE_Exp e) |>
End

Inductive resolved_block:
  ∀l1 v sl bl1 bl2 bl3 bss e.
    type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v)) ∧

    bl1 = bir_block_t l1 bss (BStmt_Jmp (BLE_Exp e)) ∧
    bl2 = cjmp_block l1 bss e v sl ∧
    bl3 = jmp_block sl e ⇒
    resolved_block l1 v sl bl1 bl2 bl3
End

Theorem resolved_block_labels:
  ∀l v sl bl1 bl2 bl3.
    resolved_block l v sl bl1 bl2 bl3 ⇒
    bl1.bb_label = l ∧ bl2.bb_label = l ∧ bl3.bb_label = BL_Label sl
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [resolved_block_cases, cjmp_block_def, jmp_block_def]
QED

Theorem resolved_block_vars:
  ∀l1 v sl bl1 bl2 bl3.
    resolved_block l1 v sl bl1 bl2 bl3 ⇒
    (bir_vars_of_block bl2 UNION bir_vars_of_block bl3)
    SUBSET bir_vars_of_block bl1
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss++PRED_SET_ss++holBACore_ss)
         [resolved_block_cases, cjmp_block_def, jmp_block_def,
          cjmp_stmtE_def, bir_vars_of_block_def,
          bir_vars_of_stmtE_def, bir_vars_of_label_exp_def]
QED

(*TODO: maybe these should be Inductive for consistency?*)

Definition direct_jump_target_block_def:
  direct_jump_target_block l bl =
  ∀es.
    es = bl.bb_last_statement ⇒
    (es = BStmt_Jmp (BLE_Label l) ∨
     ∃c l2. es = BStmt_CJmp c (BLE_Label l) l2 ∨
     ∃c l1. es = BStmt_CJmp c l1 (BLE_Label l))
End

Definition direct_jump_target_def:
  direct_jump_target l p =
  ∃l' bl.
    bir_get_current_block p (bir_block_pc l') = SOME bl ∧
    direct_jump_target_block l bl
End

Definition fresh_label_def:
  fresh_label l p =
  (~(MEM l (bir_labels_of_program p)) ∧
   ~(direct_jump_target l p))
End

Inductive resolved:
  ∀l1 v sl p p' bl1 bl2 bl3.
    fresh_label (BL_Label sl) p ∧
    (∀l. MEM l (bir_labels_of_program p') ⇔
           MEM l (bir_labels_of_program p) ∨ l = BL_Label sl) ∧

    bir_get_current_block p (bir_block_pc l1) = SOME bl1 ∧
    bir_get_current_block p' (bir_block_pc l1) = SOME bl2 ∧
    bir_get_current_block p' (bir_block_pc (BL_Label sl)) = SOME bl3 ∧
    resolved_block l1 v sl bl1 bl2 bl3 ∧

    (∀l. MEM l (bir_labels_of_program p) ∧ l ≠ l1 ⇒
         ∃bl. bir_get_current_block p (bir_block_pc l) = SOME bl ∧
              bir_get_current_block p' (bir_block_pc l) = SOME bl) ⇒

    resolved l1 v sl p p'
End

(*Any value besides 1w is fine*)
Definition assert_block_def:
  assert_block l bss v =
  <| bb_label := l;
     bb_statements := bss ++ [BStmt_Assert (BExp_Const (Imm1 0w))];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address v)) |>
End

Inductive resolved_fail_block:
  ∀l v bl1 bl2 e.
    bl1 = bir_block_t l bss (BStmt_Jmp (BLE_Exp e)) ∧
    bl2 = assert_block l bss v ⇒
    resolved_fail_block l v bl1 bl2
End

Theorem resolved_fail_block_labels:
  ∀l v bl1 bl2.
    resolved_fail_block l v bl1 bl2 ⇒
    bl1.bb_label = l ∧ bl2.bb_label = l
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [resolved_fail_block_cases, assert_block_def]
QED

Theorem resolved_fail_block_vars:
  ∀l v bl1 bl2.
    resolved_fail_block l v bl1 bl2 ⇒
    bir_vars_of_block bl2 SUBSET bir_vars_of_block bl1
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (list_ss++PRED_SET_ss++holBACore_ss)
         [resolved_fail_block_cases, assert_block_def,
          bir_vars_of_block_def, bir_vars_of_stmtE_def,
          bir_vars_of_stmtB_def,  bir_vars_of_label_exp_def]
QED

Inductive resolved_fail:
  ∀l1 v p p' bl1 bl2.
    (∀l. MEM l (bir_labels_of_program p') ⇔ MEM l (bir_labels_of_program p)) ∧

    bir_get_current_block p (bir_block_pc l1) = SOME bl1 ∧
    bir_get_current_block p' (bir_block_pc l1) = SOME bl2 ∧
    resolved_fail_block l1 v bl1 bl2 ∧

    (∀l. MEM l (bir_labels_of_program p) ∧ l ≠ l1 ⇒
         ∃bl. bir_get_current_block p (bir_block_pc l) = SOME bl ∧
              bir_get_current_block p' (bir_block_pc l) = SOME bl) ⇒

    resolved_fail l1 v p p'
End


val _ = export_theory();

