open HolKernel Parse boolLib bossLib;

open bir_programTheory bir_htTheory;
open HolBACoreSimps;

val _ = new_theory "contractTransfer";


Definition contract_simulated_def:
  contract_simulated p p' =
  ∀s l ls s' o2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒
    (∀l'. l' IN ls ⇒ MEM l' (bir_labels_of_program p)) ⇒

    bir_exec_to_labels ls p' s = BER_Ended o2 m2 n2 s' ⇒
    ~(∃l'. s'.bst_status = BST_JumpOutside l') ⇒
    (∃o1 m1 n1.
      bir_exec_to_labels ls p s = BER_Ended o1 m1 n1 s')
End

Theorem contract_transfer:
  ∀ (p' : 'a bir_program_t) l ls pre post  (p : 'a bir_program_t).
    contract_simulated p p' ⇒
    bir_vars_of_program p' = bir_vars_of_program p ⇒

    MEM l (bir_labels_of_program p) ⇒
    (∀l'. l' IN ls ⇒ MEM l' (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
SIMP_TAC std_ss [bir_exec_to_labels_triple_def] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM ‘∀s'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘s’ thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
rename1 ‘_ = BER_Ended o2 m2 n2 s'’ >>

subgoal ‘∃s1 o1 m1 n1.
           bir_exec_to_labels ls p s = BER_Ended o1 m1 n1 s'’ >- (
  ‘s.bst_pc = bir_block_pc l’ by (
    ASM_SIMP_TAC (std_ss++holBACore_ss)
      [bir_block_pc_def, bir_programcounter_t_component_equality]
  ) >>
  ‘~(∃l'. s'.bst_status = BST_JumpOutside l')’ by
    ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
  METIS_TAC [contract_simulated_def]
) >>

PROVE_TAC []
QED


val _ = export_theory();
