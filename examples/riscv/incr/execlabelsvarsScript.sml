open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open birs_auxTheory;
open HolBACoreSimps;

open pred_setTheory;

val _ = new_theory "execlabelsvars";

(*
bir-support/bir_program_vars
bir_env_EQ_FOR_VARS
!!!!!!! bir_varset_COMPL
bir_changed_vars_of_stmtB_THM
bir_changed_vars_exec_step_n_THM
*)

(*
bir_programTheory

Definition bir_exec_steps_def:
  (bir_exec_steps p state = bir_exec_steps_GEN (T, (\_. T)) p state NONE)
End

(* A simple instance that counts all steps and has a fixed no of steps given.
   We are sure it terminates, therefore, the result is converted to a tuple. *)
Definition bir_exec_step_n_def:
  bir_exec_step_n p state n =
  valOf_BER_Ended_steps (bir_exec_steps_GEN (T, (\_. T)) p state (SOME n))
End

(* We might be interested in executing a certain no of blocks. *)
Definition bir_exec_block_n_def:
  bir_exec_block_n p state n =
  valOf_BER_Ended (bir_exec_steps_GEN (F, (\pc. pc.bpc_index = 0)) p state (SOME n))
End

(* Executing till a certain set of labels is useful as well. Since we might loop
   outside this set of labels, infinite runs are possible. *)
Definition bir_exec_to_labels_n_def:
  bir_exec_to_labels_n ls p state n =
  bir_exec_steps_GEN (F, \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) p state (SOME n)
End

Definition bir_exec_to_labels_def:
  bir_exec_to_labels ls p state = bir_exec_to_labels_n ls p state 1
End
*)

(*
bir_changed_vars_exec_step_THM
TODO: make a exec_to_labels instead of bir_changed_vars_exec_step_n_THM
or maybe not....

see bir_program_varsTheory.bir_vars_exec_step_THM !!!!!!!!!!!!!!!!!!!!!!!

(bir_vars_exec_infinite_step_fun_THM)
bir_program_multistep_propsTheory.bir_exec_step_n_REWRS

--------------------

first just prove _GEN: better with def (? but maybe need ? bir_program_multistep_propsTheory.bir_exec_steps_GEN_REWR_STEP (and the terminated thm))

bir_exec_infinite_steps_COUNT_STEPS --- bir_program_multistep_propsTheory.bir_exec_infinite_steps_COUNT_STEPS_UNFOLD
bir_exec_infinite_steps_fun_COUNT_PCs --- def
bir_exec_infinite_steps_fun --- !!! bir_vars_exec_infinite_step_fun_THM !!!

then bir_exec_to_labels_n_def

*)

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
  cheat
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
