open HolKernel Parse boolLib bossLib;

open listTheory;

open bir_programTheory bir_expTheory bir_exp_immTheory;
open bir_program_blocksTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;

val _ = new_theory "resolution";


Inductive resolved_block:
  ∀l1 v sl bl1 bl2 bl3 bss e c.
    type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v)) ∧

    bl1 = bir_block_t l1 bss (BStmt_Jmp (BLE_Exp e)) ∧
    c = BExp_BinPred BIExp_Equal e (BExp_Const v) ∧
    bl2 = bir_block_t l1 bss
      (BStmt_CJmp c (BLE_Label (BL_Address v)) (BLE_Label (BL_Label sl))) ∧
    bl3 = bir_block_t (BL_Label sl) [] (BStmt_Jmp (BLE_Exp e)) ⇒
    resolved_block l1 v sl bl1 bl2 bl3
End

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
    bir_get_current_block p (bir_block_pc l') = SOME bl ⇒
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
           MEM l (bir_labels_of_program p) ∨ l = (BL_Label sl)) ∧
    (MEM (BL_Address v) (bir_labels_of_program p)) ∧

    bir_get_current_block p (bir_block_pc l1) = SOME bl1 ∧
    bir_get_current_block p' (bir_block_pc l1) = SOME bl2 ∧
    bir_get_current_block p' (bir_block_pc (BL_Label sl)) = SOME bl3 ∧
    resolved_block l1 v sl bl1 bl2 bl3 ∧

    (∀l. MEM l (bir_labels_of_program p) ∧ l ≠ l1 ⇒
         ∃bl. bir_get_current_block p (bir_block_pc l) = SOME bl ∧
              bir_get_current_block p' (bir_block_pc l) = SOME bl) ⇒

    resolved l1 v sl p p'
End


Inductive resolved_fail_block:
  ∀l v bl1 bl2 e.
    bl1 = bir_block_t l [] (BStmt_Jmp (BLE_Exp e)) ∧
    bl2 = bir_block_t l [BStmt_Assert (BExp_Const (Imm1 0w))] (BStmt_Halt v) ⇒
    resolved_fail_block l v bl1 bl2
End

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

