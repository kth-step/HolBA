open HolKernel Parse boolLib bossLib;

open bir_immTheory;
open bir_programTheory;
open bir_tsTheory;
open bir_program_multistep_propsTheory;
open holba_auxiliaryTheory;

(* From lifter: *)
open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;

(* From comp: *)
open total_program_logicTheory;
open total_ext_program_logicTheory;

open HolBASimps;
open HolBACoreSimps;
open program_logicSimps;

open holba_auxiliaryLib;

open m0_mod_stepLib;

val _ = new_theory "bir_common_backlifter";

Theorem set_of_address_in_all_address_labels_thm:
 !l adds.
    l IN {BL_Address (Imm64 ml') | ml' IN adds} ==>
    l IN {l | IS_BL_Address l}
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def]
QED

Theorem bir_exec_to_labels_TO_exec_to_addr_label_n:
   !bs' ml' mls p bs l n n0.
    (bs'.bst_pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}) ==>
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
         BER_Ended l n n0 bs') ==>
    ?n' lo c_st c_addr_labels.
         (n' > 0) /\
         (c_st = n) /\
         (bir_exec_to_addr_label_n p bs n' =
           BER_Ended lo c_st c_addr_labels bs')
Proof
REPEAT STRIP_TAC >>
subgoal `bs'.bst_pc.bpc_label IN {l | IS_BL_Address l}` >- (
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
				      bir_exec_to_labels_n_def] >>
subgoal `bir_pc_cond_impl (F,
	   (\pc.
	     (pc.bpc_index = 0) /\
	     pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls})) (F, (\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))` >- (
  FULL_SIMP_TAC std_ss [bir_pc_cond_impl_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
IMP_RES_TAC bir_exec_steps_GEN_change_cond_Ended_SOME >>
Q.EXISTS_TAC `n2` >>
FULL_SIMP_TAC arith_ss [] >>
METIS_TAC []
QED

(* Just a version of bir_is_lifted_prog_MULTI_STEP_EXEC phrased in a more handy way *)
Theorem bir_is_lifted_prog_MULTI_STEP_EXEC_compute:
  !mu bs bs' ms ml (p:'a bir_program_t) (r:(64, 8, 'b) bir_lifting_machine_rec_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog r mu mms p ==>
    bmr_rel r bs ms ==>
    MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    EVERY (bmr_ms_mem_contains r ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
    ?ms' li.
    (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
    bmr_ms_mem_unchanged r ms ms' mu /\
    EVERY (bmr_ms_mem_contains r ms') mms /\
    (bs'.bst_pc = bir_block_pc (BL_Address li)) /\
    MEM (BL_Address li) (bir_labels_of_program p) /\
    bmr_rel r bs' ms'
Proof
REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:(64, 8, 'b) bir_lifting_machine_rec_t``, ``mu:64 word_interval_t``,
                    ``mms:(word64# word8 list) list``,
                    ``p:'a bir_program_t``] bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
QED

Theorem bir_inter_exec_notin_end_label_set:
   !mls p bs l n0 n' n'' lo lo' c_st c_st' bs' bs''.
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       BER_Ended l c_st n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n'' = BER_Ended lo' c_st' n'' bs'') ==>
    c_st' < c_st ==>
    n'' > 0 ==>
    ~bir_state_is_terminated bs'' ==>
    bs''.bst_pc.bpc_label NOTIN
      {BL_Address (Imm64 ml') | ml' IN mls}
Proof
REPEAT STRIP_TAC >>
(* NOTE: The number of taken statement steps is c_st for both the to-label execution
 * and the to-addr-label-execution. *)
(* The number of PCs counted (= in mls) at c_st' statement steps must be 0. *)
subgoal `~bir_state_COUNT_PC (F,
	  (\pc.
	       (pc.bpc_index = 0) /\
	       pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}))
	      (bir_exec_infinite_steps_fun p bs c_st')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended] >>
  (* Ergo, at c_st' statement steps, the PC label is not in mls, which follows after
   * some arithmetic. *)
  QSPECL_X_ASSUM ``!(n:num). (n < c_st) ==> _`` [`c_st'`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  subgoal `c_st' > 0` >- (
    METIS_TAC [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_SOME_EQ_Ended_Running_steps,
	       bir_state_is_terminated_def]
  ) >>
  FULL_SIMP_TAC std_ss [NUM_LSONE_EQZ, bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
  QSPECL_X_ASSUM ``!j. _`` [`PRE c_st'`] >>
  SUBGOAL_THEN ``SUC (PRE (c_st':num)) = c_st'`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  METIS_TAC [NUM_PRE_LT]
) >>
(* So either PC at c_st' statement steps has index 0, or it is not in mls.
 * But PC has index 0... *)
subgoal `bs''.bst_pc.bpc_index = 0` >- (
  METIS_TAC [bir_exec_to_addr_label_n_ended_running, bir_state_is_terminated_def]
) >>
(* ... which proves the goal, after some identification of states. *)
FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def, bir_exec_to_addr_label_n_def,
		      bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
QED

val _ = export_theory ();
