open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;

open bir_valuesTheory;
open bir_expTheory;
open bir_envTheory;
open bir_programTheory;
open bir_typing_expTheory;

open bir_bool_expTheory;
open bir_exp_substitutionsTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

val _ = new_theory "bir_symb_sound";

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

(* TODO: prove soundness of this instance here (several soundness properties) *)
(*
symb_symbols_f_sound sr
symb_ARB_val_sound sr
symb_typeof_exp_sound sr
symb_mk_exp_eq_f_sound sr
symb_mk_exp_conj_f_sound sr
symb_mk_exp_symb_f_sound sr
symb_subst_f_sound sr
symb_step_sound sr
*)


val birs_exec_stmt_assign_sound_thm = store_thm(
   "birs_exec_stmt_assign_sound_thm", ``
!v ex s s' sys Pi H.
(bir_exec_stmt_assign v ex s = s') ==>
(birs_exec_stmt_assign v ex sys = Pi) ==>
(birs_symb_matchstate sys H s) ==>
(?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_assign_def, birs_exec_stmt_assign_def, birs_symb_matchstate_def] >>

  IMP_RES_TAC birs_eval_exp_sound_thm >>
  PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `ex`) >>

  FULL_SIMP_TAC (std_ss) [] >- (
    FULL_SIMP_TAC (std_ss) [] >>
    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>

    METIS_TAC [symb_interpr_for_symbs_EQ_set_typeerror_thm, birs_state_set_typeerror_def]
  ) >>

  FULL_SIMP_TAC (std_ss) [] >>
  `type_of_bir_val v' = ty` by (
    METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, birs_eval_exp_IMP_type_thm, optionTheory.option_CLAUSES]
  ) >>

  FULL_SIMP_TAC (std_ss) [pairTheory.pair_CASE_def] >>
  Cases_on `ty = bir_var_type v /\ ?x. sys.bsst_environ (bir_var_name v) = SOME x /\ type_of_bir_exp x = SOME ty` >- (
    FULL_SIMP_TAC (std_ss) [pairTheory.pair_CASE_def] >>

    (* TODO: from matchenv *)
    `bir_env_check_type v s.bst_environ` by cheat >>
    Cases_on `s.bst_environ` >>
    `f (bir_var_name v) ≠ NONE` by cheat >>
    FULL_SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def] >>

    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>
    (* TODO: fix *)
    CONJ_TAC >- cheat >>
    cheat
  ) >>

  POP_ASSUM (fn thm => (FULL_SIMP_TAC std_ss [thm] >> ASSUME_TAC thm)) >>
  `bir_env_write v v' s.bst_environ = NONE` by (
    (* TODO: from matchenv *)
    cheat
  ) >>
  FULL_SIMP_TAC (std_ss) [] >>

  PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
  PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>
  METIS_TAC [symb_interpr_for_symbs_EQ_set_typeerror_thm, birs_state_set_typeerror_def]
);

(*
val birs_exec_step_sound_thm = store_thm(
   "birs_exec_step_sound_thm", ``
!prog s s' sys Pi H.
((SND o bir_exec_step prog) s = s') ==>
(birs_exec_step prog sys = Pi) ==>
(birs_symb_matchstate sys H s) ==>
(?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
);
*)

(*
val birs_symb_step_sound_thm = store_thm(
   "birs_symb_step_sound_thm", ``
!prog. symb_step_sound (bir_symb_rec_sbir prog)
``,
  REWRITE_TAC [symb_step_sound_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `sys`) birs_symb_to_symbst_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `Pi`) birs_symb_to_symbst_SET_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [birs_symb_matchstate_EQ_thm] >>

  POP_ASSUM_LIST (ASSUME_TAC o LIST_CONJ o map (SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss)
    [bir_symb_rec_sbir_def, birs_symb_to_from_symbst_thm, birs_symb_to_from_concst_thm])) >>
  FULL_SIMP_TAC std_ss [] >>

  `(SND o bir_exec_step prog) st' = st''` by (
    METIS_TAC [birs_symb_to_concst_BIJ_thm, combinTheory.o_DEF]
  ) >>
  `(birs_exec_step prog st) = Pi_t` by (
    METIS_TAC [birs_symb_to_symbst_BIJ_thm, pred_setTheory.IMAGE_11]
  ) >>

  IMP_RES_TAC birs_exec_step_sound_thm >>
  Q.EXISTS_TAC `birs_symb_to_symbst sys'` >>
  FULL_SIMP_TAC std_ss [birs_symb_matchstate_EQ_thm] >>

  METIS_TAC [pred_setTheory.IMAGE_IN]
);
*)


val _ = export_theory();
