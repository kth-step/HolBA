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


val symb_interpr_for_symbs_IMP_UPDATE_ENV_thm = store_thm(
   "symb_interpr_for_symbs_IMP_UPDATE_ENV_thm", ``
!sys H vn sv.
  (bir_vars_of_exp sv SUBSET birs_symb_symbols sys) ==>
  (symb_interpr_for_symbs (birs_symb_symbols sys) H) ==>
  (symb_interpr_for_symbs (birs_symb_symbols (sys with bsst_environ := (vn =+ (SOME sv)) sys.bsst_environ)) H)
``,
  FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, birs_symb_symbols_def] >>
  REPEAT STRIP_TAC >>

  `bir_vars_of_exp sv SUBSET symb_interpr_dom H` by (
    METIS_TAC [pred_setTheory.SUBSET_TRANS]
  ) >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [pred_setTheory.UNION_SUBSET, pred_setTheory.BIGUNION_SUBSET] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `vn' = vn` >> (
    FULL_SIMP_TAC (std_ss) [combinTheory.UPDATE_APPLY, optionTheory.option_CLAUSES]
  ) >>
  METIS_TAC []
);

val birs_interpret_fun_IMP_birs_matchenv_thm = store_thm(
   "birs_interpret_fun_IMP_birs_matchenv_thm", ``
!H senv env vn sv v.
  (birs_interpret_fun H sv = SOME v) ==>
  (birs_matchenv H senv (BEnv (env))) ==>
  (birs_matchenv H ((vn =+ (SOME sv)) senv) (BEnv ((vn =+ (SOME v)) env)))
``,
  FULL_SIMP_TAC (std_ss) [birs_matchenv_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `vn = var` >> (
    FULL_SIMP_TAC (std_ss) [combinTheory.UPDATE_APPLY, optionTheory.option_CLAUSES, bir_env_lookup_def]
  )
);

val birs_eval_exp_IMP_varset_thm = store_thm(
   "birs_eval_exp_IMP_varset_thm", ``
!ex senv sv ty.
  (birs_eval_exp ex senv = SOME (sv,ty)) ==>
  (bir_vars_of_exp sv SUBSET (BIGUNION {bir_vars_of_exp e | (?vn. senv vn = SOME e)}))
``,
  Induct_on `ex` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [birs_eval_exp_def, LET_DEF, birs_eval_exp_subst_def, bir_vars_of_exp_def]
  ) >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [birs_senv_typecheck_thm, bir_envty_includes_vs_def, birs_envty_of_senv_def, birs_eval_exp_subst_var_def,
       bir_envty_includes_v_def, bir_vars_of_exp_def, pred_setTheory.BIGUNION, pred_setTheory.SUBSET_DEF] >>
    METIS_TAC []
  ) >> (
    REPEAT STRIP_TAC >> (
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>
      FULL_SIMP_TAC (std_ss)
        [birs_senv_typecheck_thm, bir_vars_of_exp_def, type_of_bir_exp_def, bir_envTheory.bir_envty_includes_vs_UNION] >>
      Cases_on `type_of_bir_exp ex` >> Cases_on `type_of_bir_exp ex'` >> Cases_on `type_of_bir_exp ex''` >> (
        FULL_SIMP_TAC (std_ss) [pairTheory.pair_CASE_def]
      )
    )
  ) >> (
    Cases_on `x` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [optionTheory.IS_SOME_EXISTS]
    )
  ) >>

  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [optionTheory.IS_SOME_EXISTS]
  )
);


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

  (* either both evaluation error, or both a value *)
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

  PAT_X_ASSUM ``birs_matchenv A B C`` (fn thm => (ASSUME_TAC ((Q.SPEC `bir_var_name v` o REWRITE_RULE [birs_matchenv_def]) thm) >> ASSUME_TAC thm)) >>

  (* does the environment have a value, and is it a value of the right type (and is the new value also of the right type)? *)
  FULL_SIMP_TAC (std_ss) [pairTheory.pair_CASE_def] >>
  Cases_on `(bir_env_lookup (bir_var_name v) s.bst_environ = NONE) \/
            (?r. bir_env_lookup (bir_var_name v) s.bst_environ = SOME r /\ ~(type_of_bir_val r = bir_var_type v /\ bir_var_type v = ty))` >- (
    `bir_env_write v v' s.bst_environ = NONE` by (
      Cases_on `s.bst_environ` >>
      FULL_SIMP_TAC (std_ss) [bir_env_write_def, bir_env_check_type_def, bir_env_lookup_type_def] >>
      Cases_on `type_of_bir_val r = bir_var_type v` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC (std_ss) [bir_env_update_def]
    ) >>

    (* from matchenv *)
    `~((ty = bir_var_type v) /\
       (?x. sys.bsst_environ (bir_var_name v) = SOME x /\ type_of_bir_exp x = SOME ty))` by (
      Cases_on `sys.bsst_environ (bir_var_name v) = NONE` >> (
        FULL_SIMP_TAC (std_ss) [birs_matchenv_def]
      ) >> (
        PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `bir_var_name v`) >>
        FULL_SIMP_TAC (std_ss) [] >>
        REV_FULL_SIMP_TAC (std_ss) []
      ) >>

      Cases_on `type_of_bir_val r = bir_var_type v` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      Cases_on `ty = bir_var_type v` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, optionTheory.option_CLAUSES]
    ) >>

    PAT_X_ASSUM ``A \/ (?B. C /\ D)`` (K ALL_TAC) >>
    POP_ASSUM (fn thm => FULL_SIMP_TAC (std_ss) [thm]) >>

    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>
    METIS_TAC [symb_interpr_for_symbs_EQ_set_typeerror_thm, birs_state_set_typeerror_def]
  ) >> (
    FULL_SIMP_TAC (std_ss) [] >>
    `?env. bir_env_write v v' s.bst_environ = SOME env` by (
      Cases_on `s.bst_environ` >>
      FULL_SIMP_TAC (std_ss) [bir_env_write_def, bir_env_check_type_def, bir_env_lookup_type_def] >>
      FULL_SIMP_TAC (std_ss) [bir_env_update_def, bir_env_lookup_def]
    ) >>

    (* from matchenv *)
    `(ty = bir_var_type v) /\
     (?x. sys.bsst_environ (bir_var_name v) = SOME x /\ type_of_bir_exp x = SOME ty)` by (

      PAT_X_ASSUM ``birs_matchenv A B C`` (ASSUME_TAC o Q.SPEC `bir_var_name v` o REWRITE_RULE [birs_matchenv_def]) >>
      FULL_SIMP_TAC (std_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss) [] >>

      METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, optionTheory.option_CLAUSES]
    ) >>

    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>

    CONJ_TAC >- (
      `bir_vars_of_exp sv SUBSET birs_symb_symbols sys` by (
        FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def] >>
        IMP_RES_TAC birs_eval_exp_IMP_varset_thm >>
        METIS_TAC [pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION]
      ) >>
      METIS_TAC [symb_interpr_for_symbs_IMP_UPDATE_ENV_thm]
    ) >>

    Cases_on `s.bst_environ` >>
    FULL_SIMP_TAC (std_ss) [optionTheory.option_CLAUSES, bir_env_write_def, bir_env_update_def] >>
    METIS_TAC [birs_interpret_fun_IMP_birs_matchenv_thm]
  )
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
