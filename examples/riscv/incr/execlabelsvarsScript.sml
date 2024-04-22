open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open birs_auxTheory;
open HolBACoreSimps;

open pred_setTheory;

val _ = new_theory "execlabelsvars";

Theorem bir_vars_state_COUNT_PC_THM:
  !vs st1 st2 pc_cond.
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_COUNT_PC pc_cond st1 =
     bir_state_COUNT_PC pc_cond st2)
Proof
  REPEAT STRIP_TAC >>
  Cases_on `pc_cond` >>
  FULL_SIMP_TAC (std_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_COUNT_PC_def]
QED

Theorem bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM:
  !vs st1 st2 pc_cond p i.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st1 i =
     bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st2 i)
Proof
  Induct_on `i` >> (
    REWRITE_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_def]
  ) >>
  REPEAT STRIP_TAC >>

  IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] bir_program_varsTheory.bir_vars_exec_step_state_THM) >>
  PAT_X_ASSUM ``!x. A`` (IMP_RES_TAC) >>
  IMP_RES_TAC bir_vars_state_COUNT_PC_THM >>
  REPEAT (PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPEC `pc_cond`)) >>

  FULL_SIMP_TAC std_ss [LET_THM]
QED

Theorem bir_vars_exec_infinite_steps_COUNT_STEPS_THM:
  !vs st1 st2 pc_cond p max_steps_opt.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st1 =
     bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st2)
Proof
  REPEAT STRIP_TAC >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st1` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_EQ_NONE] >>
    GEN_TAC >>
    POP_ASSUM (ASSUME_TAC o Q.SPEC `i`) >>
    FULL_SIMP_TAC std_ss [] >>
    IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
    IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_infinite_step_fun_THM >>
    METIS_TAC [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
  ) >>

  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_EQ_SOME] >> (
    STRIP_TAC >- (
      IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
      IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_infinite_step_fun_THM >>
      METIS_TAC [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
    ) >>
    ASM_SIMP_TAC std_ss [] >>
    POP_ASSUM (fn t => GEN_TAC >> DISCH_TAC >> IMP_RES_TAC t) >>
    STRIP_TAC >> (
      IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_infinite_step_fun_THM >>
      IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
      METIS_TAC [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
    )
  )
QED

Theorem bir_vars_exec_steps_observe_llist_aux_THM:
  !vs st1 st2 p i.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (FST (bir_exec_step p (bir_exec_infinite_steps_fun p st1 i)) =
     FST (bir_exec_step p (bir_exec_infinite_steps_fun p st2 i)))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_infinite_step_fun_THM >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `i`) >>
  IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_step_THM >>

  Cases_on `bir_exec_step p (bir_exec_infinite_steps_fun p st1 i)` >>
  Cases_on `bir_exec_step p (bir_exec_infinite_steps_fun p st2 i)` >>
  FULL_SIMP_TAC std_ss [LET_THM]
QED

Theorem bir_vars_exec_steps_observe_llist_THM:
  !vs st1 st2 p step_no.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_steps_observe_llist p st1 step_no =
     bir_exec_steps_observe_llist p st2 step_no)
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_steps_observe_llist_aux_THM >>
  ASM_SIMP_TAC std_ss [bir_exec_steps_observe_llist_def]
QED

Theorem bir_vars_exec_steps_GEN_THM:
  !vs st1 st2 pc_cond p max_steps_opt.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_steps_GEN pc_cond p st1 max_steps_opt, bir_exec_steps_GEN pc_cond p st2 max_steps_opt) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_infinite_steps_COUNT_STEPS_THM >>
  IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
  IMP_RES_TAC bir_vars_exec_steps_observe_llist_THM >>

  ASM_REWRITE_TAC [bir_exec_steps_GEN_def] >>
  Q.ABBREV_TAC `step_no = bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st2` >>
  Q.ABBREV_TAC `ll = bir_exec_steps_observe_llist p st2 step_no` >>
  FULL_SIMP_TAC std_ss [LET_THM] >>

  CASE_TAC >>
  METIS_TAC [bir_program_varsTheory.bir_vars_exec_infinite_step_fun_THM]
QED

Theorem bir_vars_exec_to_labels_n_THM:
  !vs st1 st2 p ls n.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_to_labels_n ls p st1 n, bir_exec_to_labels_n ls p st2 n) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REWRITE_TAC [bir_exec_to_labels_n_def, bir_vars_exec_steps_GEN_THM]
QED

Theorem bir_vars_exec_to_labels_THM:
  !ls p vs st1 st2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_to_labels ls p st1, bir_exec_to_labels ls p st2) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REWRITE_TAC [bir_exec_to_labels_def, bir_vars_exec_to_labels_n_THM]
QED

Theorem bir_vars_exec_to_labels_spec_THM:
  !ls p vs st1 st2 ol n n' st1'.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_to_labels ls p st1 = BER_Ended ol n n' st1') ==>
    ?st2'. bir_exec_to_labels ls p st2 = BER_Ended ol n n' st2' /\
           bir_state_EQ_FOR_VARS vs st1' st2'
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_to_labels_THM >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `ls`) >>

  Cases_on `bir_exec_to_labels ls p st2` >> (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_execution_result_t_11, pairTheory.pair_CASE_def]
  )
QED

val _ = export_theory ();
