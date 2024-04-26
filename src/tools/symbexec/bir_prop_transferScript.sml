open HolKernel boolLib Parse bossLib;

open pred_setTheory;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;
open bir_symb_sound_coreTheory;

open HolBACoreSimps;
open bir_tsTheory;
open program_logicSimps;

val _ = new_theory "bir_prop_transfer";

Theorem bir_vars_bir_ts_thm:
  !ls p vs st1 st2 st1'.
    (vs = bir_vars_of_program p) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    ((bir_ts p).weak ls st1 st1') ==>
    ?st2'. (bir_ts p).weak ls st2 st2' /\
           bir_state_EQ_FOR_VARS vs st1' st2'
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_program_varsTheory.bir_vars_exec_to_labels_spec2_THM >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_ts_def, bir_weak_trs_def] >>
  Cases_on `bir_exec_to_labels ls p st1` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_execution_result_t_11, pairTheory.pair_CASE_def]
  ) >>

  PAT_X_ASSUM ``!x. A`` (IMP_RES_TAC) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_execution_result_t_11, pairTheory.pair_CASE_def] >>
  METIS_TAC [bir_programTheory.bir_state_is_terminated_def, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
QED

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

Theorem bir_Pi_overapprox_Q_thm:
  !p P sys Pi Q.
  (Pi_overapprox_Q (bir_symb_rec_sbir p) P (birs_symb_to_symbst sys) (IMAGE birs_symb_to_symbst Pi) Q)
  <=>
  (!sys2 bs bs' H.
     sys2 IN Pi ==>
     birs_symb_matchstate sys H bs ==>
     (\bs. P (birs_symb_to_concst bs)) bs ==>
     (?H'. symb_interpr_ext H' H /\ birs_symb_matchstate sys2 H' bs') ==>
     (\bs bs'. Q (birs_symb_to_concst bs) (birs_symb_to_concst bs')) bs bs')
Proof
FULL_SIMP_TAC (std_ss++birs_state_ss) [Pi_overapprox_Q_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>

  EQ_TAC >- (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`birs_symb_to_symbst sys2`, `birs_symb_to_concst bs`, `birs_symb_to_concst bs'`, `H`]) >>

    REV_FULL_SIMP_TAC (std_ss) [IMAGE_IN, symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
    METIS_TAC []
  ) >>

  REPEAT STRIP_TAC >>

  `?bsys. sys' = birs_symb_to_symbst bsys` by (
    METIS_TAC [birs_symb_to_symbst_EXISTS_thm]
  ) >>
  `?bs.  s  = birs_symb_to_concst bs /\
   ?bs'. s' = birs_symb_to_concst bs'` by (
    METIS_TAC [birs_symb_to_concst_EXISTS_thm]
  ) >>

  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`bsys`, `bs`, `bs'`, `H`]) >>

  `bsys IN Pi` by (
    FULL_SIMP_TAC std_ss [] >>

    `birs_symb_from_symbst o birs_symb_to_symbst = I` by (
      SIMP_TAC std_ss [combinTheory.o_DEF, bir_symbTheory.birs_symb_to_from_symbst_thm] >>
      MATCH_MP_TAC boolTheory.EQ_EXT >>
      SIMP_TAC std_ss [combinTheory.I_THM]
    ) >>
    METIS_TAC [IMAGE_IN, IMAGE_IMAGE, bir_symbTheory.birs_symb_to_from_symbst_thm, IMAGE_I]
  ) >>

  FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
  REV_FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
  METIS_TAC []
QED


val _ = export_theory();
