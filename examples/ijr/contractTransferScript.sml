open HolKernel Parse boolLib bossLib BasicProvers;

open listTheory pred_setTheory pred_setSimps;

open bir_programTheory bir_htTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;
open bir_wm_instTheory holba_auxiliaryTheory;
open abstract_simp_hoare_logicTheory abstract_hoare_logicTheory;
open abstract_hoare_logicSimps bir_program_env_orderTheory bir_env_oldTheory;
open holba_auxiliaryLib;

open resolutionTheory simulationTheory simulationFailTheory;

val _ = new_theory "contractTransfer";


Definition simulated_termination_def:
  simulated_termination (p: 'a bir_program_t) (p': 'a bir_program_t) =
  ∀s l s' o2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒

    exec_to_prog p' s p = BER_Ended o2 m2 n2 s' ⇒
    ~(bir_state_is_terminated s') ⇒
    (∃o1 m1 n1.
      exec_to_prog p s p = BER_Ended o1 m1 n1 s')
End

Theorem simulated_termination_REFL:
  ∀p. simulated_termination p p
Proof
SIMP_TAC (std_ss++holBACore_ss) [simulated_termination_def]
QED

Theorem simulated_simulated_termination:
  ∀p p'. simulated p p' ⇒ simulated_termination p p'
Proof
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [simulated_def, simulated_termination_def,
               bir_state_is_terminated_def]
QED

Theorem simulated_fail_simulated_termination:
  ∀p p'. simulated_fail p p' ⇒ simulated_termination p p'
Proof
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [simulated_fail_def, simulated_termination_def,
               bir_state_is_terminated_def]
QED

Definition exec_to_prog_n_def:
  exec_to_prog_n p s pls n =
  bir_exec_to_labels_n (set (bir_labels_of_program pls)) p s n
End

(*TODO: Strenthen simulation definitions wrt observations and steps?*)
Definition simulated_termination_n_def:
  simulated_termination_n p p' =
  ∀n s l s' os2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒

    exec_to_prog_n p' s p n = BER_Ended os2 m2 n2 s' ⇒
    ~(bir_state_is_terminated s') ⇒
    (∃os1 m1 n1.
      exec_to_prog_n p s p n = BER_Ended os1 m1 n1 s')
End

Theorem simulated_termination_simulated_termination_n:
  ∀p p'. simulated_termination p p' ⇒ simulated_termination_n p p'
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [simulated_termination_n_def, exec_to_prog_n_def] >>
Q.ABBREV_TAC ‘ls = bir_labels_of_program p’ >>

Induct_on ‘n’ >- (
  SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_0]
) >>

REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_SUC] >>

(*Program p' takes a step*)
Cases_on ‘bir_exec_to_labels (set ls) p' s’ >>
SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 ‘_ = BER_Ended os21 m21 n21 s2’ >>

(*There is a contradiction or p takes the same step*)
Cases_on ‘bir_state_is_terminated s2’ >- (
  FULL_SIMP_TAC (list_ss++holBACore_ss) [bir_state_is_terminated_def,
                                         bir_exec_to_labels_n_REWR_TERMINATED] >>
  STRIP_TAC >> FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
subgoal ‘(∃os11 m11 n11.
            bir_exec_to_labels (set ls) p s = BER_Ended os11 m11 n11 s2)’ >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [simulated_termination_def, exec_to_prog_def]
) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>

(*Program p' takes the rest of the steps*)
Cases_on ‘bir_exec_to_labels_n (set ls) p' s2 n’ >>
SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 ‘_ = BER_Ended os22 m22 n22 s2'’ >>
NTAC 2 STRIP_TAC >>

(*Program p takes the same rest of steps*)
subgoal ‘∃os12 m12 n12.
           bir_exec_to_labels_n (set ls) p s2 n = BER_Ended os12 m12 n12 s2'’ >- (
  subgoal ‘∃l'. s2.bst_pc = bir_block_pc l' ∧ MEM l' ls’ >- (
    MP_TAC (Q.SPECL [‘set ls’, ‘p'’, ‘s’, ‘os21’, ‘1’, ‘m21’, ‘n21’, ‘s2’]
                    bir_exec_to_labels_n_ended_running) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_block_pc_def, bir_exec_to_labels_def,
                   bir_programcounter_t_component_equality]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [exec_to_prog_n_def]
) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem bir_exec_to_labels_expand_labels:
  ∀ls ls' p s s' os c1 c2.
    ~bir_state_is_terminated s' ⇒
    ls SUBSET ls' ⇒
    bir_exec_to_labels ls p s = BER_Ended os c1 c2 s' ⇒
    (∃n c2'.
       n > 0 ∧
       bir_exec_to_labels_n ls' p s n = BER_Ended os c1 c2' s' ∧
       (∀n'. 0 < n' ∧ n' < n ⇒
             ∃s'' os' c1' c2''.
               bir_exec_to_labels_n ls' p s n' = BER_Ended os' c1' c2'' s'' ∧
               ~(s''.bst_pc.bpc_label IN ls)))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_change_labels >>
rename1 ‘bir_exec_to_labels_n _ _ _ n = BER_Ended _ _ c2' s''’ >>
Q.LIST_EXISTS_TAC [‘n’, ‘c2'’] >>
FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>

(* 1. Prove that the Ended result of the conclusion exists. *)
subgoal ‘∃s' os1 c11 c21'.
           bir_exec_to_labels_n ls' p s n' = BER_Ended os1 c11 c21' s'’ >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
  PROVE_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_SOME]
) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>

(* 2. Prove that the state reached by n'-to-label steps to ls' is not in ls *)
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
‘c11 < c1’ by METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_steps_taken] >>
‘~bir_state_is_terminated s'’ by PROVE_TAC [bir_exec_steps_GEN_SOME_EQ_Ended] >>
Q.PAT_X_ASSUM ‘bir_exec_steps_gen _ _ _ (SOME n) = _’ (K ALL_TAC) >>

Q.SUBGOAL_THEN ‘~bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0 ∧ pc.bpc_label IN ls))
                (bir_exec_infinite_steps_fun p s c11)’
  MP_TAC >- (
  subgoal ‘0 < c11’ >- (
    IMP_RES_TAC bir_exec_steps_GEN_SOME_EQ_Ended_Running_steps >>
    ASM_SIMP_TAC arith_ss []
  ) >>
  METIS_TAC [bir_exec_steps_GEN_1_EQ_Ended]
) >>
Q.PAT_X_ASSUM ‘_ = BER_Ended os c1 c2 s''’ (K ALL_TAC) >>

FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_SOME_EQ_Ended, bir_state_is_terminated_def] >>
REPEAT (Q.PAT_X_ASSUM ‘∀n. _’ (K ALL_TAC)) >>
Q.PAT_X_ASSUM ‘c21' = _’ (ASSUME_TAC o GSYM) >>
Q.PAT_X_ASSUM ‘s' = _’ (ASSUME_TAC o GSYM) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_COUNT_PC_def] >>
DISCH_THEN MATCH_MP_TAC >>
‘c21' = n'’ by ASM_SIMP_TAC arith_ss [] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_COUNT_PC_def]
QED

(*bir_exec_to_labels_restrict_labels and bir_exec_to_labels_n_restrict_labels can
 probably be proved more succinctly using the same strategy as in bir_exec_to_labels_expand_labels*)

Theorem bir_exec_to_labels_restrict_labels:
  ∀ls ls' p s s' os c1 c2.
    ls SUBSET ls' ⇒
    bir_exec_to_labels ls' p s = BER_Ended os c1 c2 s' ⇒
    s'.bst_pc.bpc_label IN ls ⇒
    ~bir_state_is_terminated s' ⇒
    (∃os' c1' c2'. bir_exec_to_labels ls p s = BER_Ended os' c1' c2' s')
Proof
REPEAT STRIP_TAC >>
subgoal ‘bir_weak_trs ls' p s = SOME s'’ >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def]
) >>
Q.SUBGOAL_THEN ‘bir_weak_trs ls p s = SOME s'’ MP_TAC >- (
  ‘weak_model (bir_etl_wm p)’ by PROVE_TAC [bir_model_is_weak] >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [weak_model_def, bir_etl_wm_def] >>
  POP_ASSUM (K ALL_TAC) >>

  Q.EXISTS_TAC ‘n’ >>
  RW_TAC std_ss [] >>
  PROVE_TAC [SUBSET_DEF]
) >>
SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def, bir_etl_wm_def] >>
REPEAT CASE_TAC
QED

Theorem bir_exec_to_labels_n_restrict_labels:
  ∀ls ls' n p s s' os c1 c2.
    ls SUBSET ls' ⇒
    n > 0 ⇒
    bir_exec_to_labels_n ls' p s n = BER_Ended os c1 c2 s' ⇒
    s'.bst_pc.bpc_label IN ls ⇒
    ~bir_state_is_terminated s' ⇒
    (∀n'. 0 < n' ∧ n' < n ⇒
          ∃s'' os' c1' c2''.
            bir_exec_to_labels_n ls' p s n' = BER_Ended os' c1' c2'' s'' ∧
            ~(s''.bst_pc.bpc_label IN ls)) ⇒
    (∃os' c1' c2'. bir_exec_to_labels ls p s = BER_Ended os' c1' c2' s')
Proof
Induct_on ‘n’ >>
REPEAT GEN_TAC >>
SIMP_TAC arith_ss [bir_exec_to_labels_n_REWR_SUC] >>
REPEAT CASE_TAC >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM ‘b' = s'’ SUBST_ALL_TAC >>
rename1 ‘bir_exec_to_labels_n _ _ _ _ = BER_Ended os2 c12 c22 s''’ >>
rename1 ‘bir_exec_to_labels _ _ _ = BER_Ended os1 c11 c21 s'’ >>

(*Execution one step*)
Cases_on ‘n = 0’ >- (
  FULL_SIMP_TAC (arith_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_0] >>
  PROVE_TAC [bir_exec_to_labels_restrict_labels]
) >>

(*Execution multiple steps*)
(*Use induction hypothesis*)
Q.PAT_X_ASSUM ‘∀ls. ∀ls'. _’ (MP_TAC o Q.SPECL [‘ls’, ‘ls'’, ‘p’, ‘s'’]) >>
ASM_SIMP_TAC (arith_ss++holBACore_ss) [] >>
Q.SUBGOAL_THEN ‘∀n'.
                  0 < n' ∧ n' < n ⇒
                  ∃s'' os' c1' c2''.
                    bir_exec_to_labels_n ls' p s' n' = BER_Ended os' c1' c2'' s'' ∧
                    s''.bst_pc.bpc_label ∉ ls’
  (fn thm => RW_TAC std_ss [thm])>- (
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM ‘∀n'. _’ (MP_TAC o Q.SPEC ‘SUC n'’) >>
  ASM_SIMP_TAC (arith_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_SUC] >>
  CASE_TAC
) >>
Q.PAT_X_ASSUM ‘bir_exec_to_labels_n ls' _ s' _ = _’ (K ALL_TAC) >>

(*Use weakness assumption*)
subgoal ‘s'.bst_pc.bpc_label NOTIN ls’ >- (
  Q.PAT_X_ASSUM ‘∀n'. _’ (MP_TAC o Q.SPEC ‘1’) >>
  ASM_SIMP_TAC (arith_ss++holBACore_ss) [GSYM bir_exec_to_labels_def]
) >>

(*Convert transitions*)
subgoal ‘bir_weak_trs ls' p s = SOME s'’ >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def,
                                        bir_exec_to_labels_n_REWR_TERMINATED] >>
  PROVE_TAC []
) >>
Q.PAT_X_ASSUM ‘bir_exec_to_labels ls' _ s = _’ (K ALL_TAC) >>
subgoal ‘bir_weak_trs ls p s' = SOME s''’ >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def]
) >>
Q.PAT_X_ASSUM ‘bir_exec_to_labels ls _ s' = _’ (K ALL_TAC) >>

(*Use weak model property*)
Q.SUBGOAL_THEN ‘bir_weak_trs ls p s = SOME s''’ MP_TAC >- (
  ‘weak_model (bir_etl_wm p)’ by PROVE_TAC [bir_model_is_weak] >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [weak_model_def, bir_etl_wm_def] >>
  POP_ASSUM (K ALL_TAC) >>
  rename1 ‘FUNPOW_OPT _ n2 s = _’ >>
  rename1 ‘FUNPOW_OPT _ n3 s' = _’ >>

  (*Show existance*)
  Q.EXISTS_TAC ‘n3 + n2’ >>
  CONJ_TAC >- (
    ‘n3 + n2 > 0’ by ASM_SIMP_TAC arith_ss [] >>
    PROVE_TAC [FUNPOW_OPT_ADD_thm]
  ) >>
  REPEAT STRIP_TAC >>
  rename1 ‘n1 < _ + _’ >>

  Cases_on ‘n1 < n2’ >- (
    PROVE_TAC [SUBSET_DEF]
  ) >>
  
  (*n1 >= n2*)
  subgoal ‘∃m. n1 = n2 + m’ >- (
    ‘n2 ≤ n1’ by ASM_SIMP_TAC arith_ss [] >>
    PROVE_TAC [arithmeticTheory.LESS_EQUAL_ADD]
  ) >>
  ASM_SIMP_TAC std_ss [] >>
  Q.PAT_X_ASSUM ‘∀n'. _’ (MP_TAC o Q.SPEC ‘m’) >>
  ASM_SIMP_TAC arith_ss [] >>
  
  (*n1 = n2*)
  Cases_on ‘m = 0’ >- (
    ASM_SIMP_TAC std_ss []
  ) >>

  (*n1 > n2*)
  ASM_SIMP_TAC arith_ss [] >>
  PROVE_TAC [FUNPOW_OPT_ADD_thm, arithmeticTheory.ADD_COMM]
) >>

ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def, bir_etl_wm_def] >>
REPEAT CASE_TAC
QED

Theorem simulated_termination_transitive:
  ∀p1 p2 p3.
    set (bir_labels_of_program p1) SUBSET set (bir_labels_of_program p2) ⇒
    simulated_termination p1 p2 ∧
    simulated_termination p2 p3 ⇒
    simulated_termination p1 p3
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [simulated_termination_def, exec_to_prog_def] >>
Q.ABBREV_TAC ‘pls1 = set (bir_labels_of_program p1)’ >>
Q.ABBREV_TAC ‘pls2 = set (bir_labels_of_program p2)’ >>

(*Expand label set*)
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [‘pls1’, ‘pls2’, ‘p3’, ‘s’, ‘s'’, ‘o2’, ‘m2’, ‘n2’]
                bir_exec_to_labels_expand_labels) >>
ASM_SIMP_TAC std_ss [] >> STRIP_TAC >>
rename1 ‘_ = BER_Ended _ _ n2' _’ >>

(*Use simulation hypothesis*)
subgoal ‘∃os1 m1 n1. bir_exec_to_labels_n pls2 p2 s n =
                     BER_Ended os1 m1 n1 s'’ >- (
  Q.SUBGOAL_THEN ‘simulated_termination_n p2 p3’ MP_TAC >- (
    PROVE_TAC [simulated_termination_simulated_termination_n]
  ) >>
  ASM_SIMP_TAC std_ss [simulated_termination_n_def, exec_to_prog_n_def] >>
  PROVE_TAC [SUBSET_DEF]
) >>

(*Restrict label set*)
subgoal ‘∃os1' m1' n1'.bir_exec_to_labels pls1 p2 s = BER_Ended os1' m1' n1' s'’ >- (
  IRULE_TAC bir_exec_to_labels_n_restrict_labels >>
  ASM_SIMP_TAC std_ss [] >>
  CONJ_TAC >- (
    ‘(1:num) > 0’ by SIMP_TAC arith_ss [] >>
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_labels_n_ended_running]
  ) >>

  Q.LIST_EXISTS_TAC [‘m1’, ‘n1’, ‘pls2’, ‘n’, ‘os1’] >> CONJ_TAC >- (
    REPEAT STRIP_TAC >>
    Q.PAT_X_ASSUM ‘∀n'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘n'’ thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    subgoal ‘~bir_state_is_terminated s''’ >- (
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
      IMP_RES_TAC bir_exec_steps_GEN_decrease_max_steps_Ended_terminated
    ) >>

    subgoal ‘∃os' c1' c2''. bir_exec_to_labels_n pls2 p2 s n' =
                            BER_Ended os' c1' c2'' s''’ >- (
      Q.SUBGOAL_THEN ‘simulated_termination_n p2 p3’ MP_TAC >- (
        PROVE_TAC [simulated_termination_simulated_termination_n]
      ) >>
      ASM_SIMP_TAC std_ss [simulated_termination_n_def, exec_to_prog_n_def] >>
      PROVE_TAC [SUBSET_DEF]
    ) >>

    PROVE_TAC []
  ) >>

  ASM_SIMP_TAC std_ss []
) >>

METIS_TAC [simulated_termination_def, exec_to_prog_def]
QED

Definition simulated_contract_def:
  simulated_contract p p' =
  ∀s l ls s' os2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels ls p' s = BER_Ended os2 m2 n2 s' ⇒
    ~(bir_state_is_terminated s') ⇒
    (∃os1 m1 n1.
      bir_exec_to_labels ls p s = BER_Ended os1 m1 n1 s')
End

Theorem simulated_termination_simulated_contract:
  ∀p p'. simulated_termination p p' ⇒ simulated_contract p p'
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [simulated_contract_def, exec_to_prog_n_def] >>
Q.ABBREV_TAC ‘pls = bir_labels_of_program p’ >>

(*Expand label set*)
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [‘ls’, ‘set pls’, ‘p'’, ‘s’, ‘s'’, ‘os2’, ‘m2’, ‘n2’]
                bir_exec_to_labels_expand_labels) >>
ASM_SIMP_TAC std_ss [] >> STRIP_TAC >>
rename1 ‘_ = BER_Ended _ _ n2' _’ >>

(*Use simulation hypothesis*)
subgoal ‘∃os1 m1 n1. bir_exec_to_labels_n (set pls) p s n =
                     BER_Ended os1 m1 n1 s'’ >- (
  METIS_TAC [simulated_termination_simulated_termination_n,
             simulated_termination_n_def, exec_to_prog_n_def]
) >>

(*Restrict label set*)
subgoal ‘∃os1' m1' n1'. bir_exec_to_labels ls p s = BER_Ended os1' m1' n1' s'’ >- (
  IRULE_TAC bir_exec_to_labels_n_restrict_labels >>
  ASM_SIMP_TAC std_ss [] >>
  CONJ_TAC >- (
    ‘(1:num) > 0’ by SIMP_TAC arith_ss [] >>
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_labels_n_ended_running]
  ) >>

  Q.LIST_EXISTS_TAC [‘m1’, ‘n1’, ‘set pls’, ‘n’, ‘os1’] >> CONJ_TAC >- (
    REPEAT STRIP_TAC >>
    Q.PAT_X_ASSUM ‘∀n'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘n'’ thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    subgoal ‘~bir_state_is_terminated s''’ >- (
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
      IMP_RES_TAC bir_exec_steps_GEN_decrease_max_steps_Ended_terminated
    ) >>

    subgoal ‘∃os' c1' c2''. bir_exec_to_labels_n (set pls) p s n' =
                            BER_Ended os' c1' c2'' s''’ >- (
      METIS_TAC [simulated_termination_simulated_termination_n,
                 simulated_termination_n_def, exec_to_prog_n_def]
    ) >>

    PROVE_TAC []
  ) >>

  ASM_SIMP_TAC std_ss []
) >>
PROVE_TAC []
QED

Theorem bir_exec_to_labels_triple_transfer:
  ∀ p p' l ls pre post.
    simulated_termination p p' ⇒
    (bir_vars_of_program p') SUBSET (bir_vars_of_program p) ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
SIMP_TAC std_ss [bir_exec_to_labels_triple_def] >>
REPEAT STRIP_TAC >>

Q.PAT_X_ASSUM ‘∀s'. _’ (MP_TAC o Q.SPEC ‘s’) >>
subgoal ‘bir_env_vars_are_initialised s.bst_environ (bir_vars_of_program p')’ >- (
  PROVE_TAC [bir_env_vars_are_initialised_SUBSET]
) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>
rename1 ‘_ = BER_Ended o2 m2 n2 s'’ >>

subgoal ‘∃s1 o1 m1 n1. bir_exec_to_labels ls p s =
                       BER_Ended o1 m1 n1 s'’ >- (
  ‘s.bst_pc = bir_block_pc l’ by (
    ASM_SIMP_TAC (std_ss++holBACore_ss)
                 [bir_block_pc_def,
                  bir_programcounter_t_component_equality]
  ) >>
  ‘~(bir_state_is_terminated s')’ by ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
  METIS_TAC [simulated_termination_simulated_contract, simulated_contract_def]
) >>

ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem contract_transfer:
  ∀ p p' i l ls ls' pre post.
    simulated_termination p p' ⇒
    (bir_vars_of_program p') SUBSET (bir_vars_of_program p) ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒
    ls' SUBSET (set (bir_labels_of_program p)) ⇒

    bir_simp_jgmt p' i l ls ls' pre post ⇒
    bir_simp_jgmt p i l ls ls' pre post
Proof
SIMP_TAC (std_ss++bir_wm_SS)
         [bir_simp_jgmt_def, abstract_simp_jgmt_def,
          abstract_jgmt_def, bir_etl_wm_def, bir_weak_trs_def] >>
REPEAT STRIP_TAC >>

Q.PAT_X_ASSUM ‘∀s'. _’ (MP_TAC o Q.SPEC ‘s’) >>
Q.SUBGOAL_THEN ‘bir_exec_to_labels_triple_precond s pre p'’
  (fn thm => ASM_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  PROVE_TAC [bir_env_vars_are_initialised_SUBSET]
) >>
Q.SUBGOAL_THEN ‘bir_exec_to_labels_triple_precond s i p'’
  (fn thm => SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  PROVE_TAC [bir_env_vars_are_initialised_SUBSET]
) >>
NTAC 2 CASE_TAC >>
REPEAT STRIP_TAC >>
rename1 ‘_ = BER_Ended o2 m2 n2 s'’ >>

subgoal  ‘∃s1 o1 m1 n1. bir_exec_to_labels (ls ∪ ls') p s =
                               BER_Ended o1 m1 n1 s'’  >- (
  subgoal ‘s.bst_pc = bir_block_pc l’ >- (
    ASM_SIMP_TAC (std_ss++holBACore_ss)
                 [bir_block_pc_def,
                  bir_programcounter_t_component_equality] >>
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def]
  ) >>
  ‘ls ∪ ls' ⊆ set (bir_labels_of_program p)’ by PROVE_TAC [UNION_SUBSET] >>
  METIS_TAC [simulated_contract_def, simulated_termination_simulated_contract]
) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>

STRIP_TAC >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def,
                        bir_exec_to_labels_triple_postcond_def] >>
  PROVE_TAC [bir_env_vars_are_initialised_ORDER,
             bir_exec_to_labels_def, bir_exec_to_labels_n_ENV_ORDER]
) >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
PROVE_TAC [bir_env_vars_are_initialised_ORDER,
           bir_exec_to_labels_def, bir_exec_to_labels_n_ENV_ORDER]
QED


val _ = export_theory();

