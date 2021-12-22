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
open bir_envTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open pred_setTheory;
open combinTheory;
open optionTheory;
open pairTheory;
open finite_mapTheory;

open HolBACoreSimps;
open symb_typesLib;

open pred_setSimps;

val _ = new_theory "bir_symb_sound";

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);


(*
=========================================================================
symb_symbols_f_sound sr
=========================================================================
 *)


val symb_interprs_eq_for_IMP_EQ_birs_interpret_subst_fmap_thm = store_thm(
   "symb_interprs_eq_for_IMP_EQ_birs_interpret_subst_fmap_thm", ``
!H H' e.
  (symb_interprs_eq_for H H' (bir_vars_of_exp e)) ==>
  (birs_interpret_subst_fmap H e = birs_interpret_subst_fmap H' e)
``,
  FULL_SIMP_TAC (std_ss++holBACore_ss) [symb_interprs_eq_for_def] >>
  REPEAT STRIP_TAC >>

(*
  (fn g as (_, tm) => MP_TAC (SPECL [(fst o dest_eq) tm, (snd o dest_eq) tm] (INST_TYPE [Type.alpha |-> ``:bir_var_t``, Type.beta |-> ``:bir_exp_t``] fmap_EQ_THM)) g) >>
*)
  REWRITE_TAC [GSYM fmap_EQ_THM] >>

  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [birs_interpret_subst_fmap_def, FUN_FMAP_DEF, bir_vars_of_exp_FINITE]
  ) >>

  
  `(x IN symb_interpr_dom H) = (x IN symb_interpr_dom H')` by (
    METIS_TAC [symb_interpr_dom_thm]
  ) >>
  ASM_REWRITE_TAC []
);

val birs_symb_symbols_f_sound_thm = store_thm(
   "birs_symb_symbols_f_sound_thm", ``
!prog.
  symb_symbols_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_symbols_f_sound_def, bir_symb_rec_sbir_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_subst_def] >>

  METIS_TAC [symb_interprs_eq_for_IMP_EQ_birs_interpret_subst_fmap_thm]
);


(*
=========================================================================
symb_ARB_val_sound sr
=========================================================================
 *)

val birs_symb_ARB_val_sound_thm = store_thm(
   "birs_symb_ARB_val_sound_thm", ``
!prog.
  symb_ARB_val_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_ARB_val_sound_def, bir_symb_rec_sbir_def] >>
  Cases_on `t` >> (
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_default_def, type_of_bir_val_def]
    )
  )
);


(*
=========================================================================
symb_typeof_exp_sound sr
=========================================================================
 *)

val birs_interpret_subst_fmap_type_sound_thm = store_thm(
   "birs_interpret_subst_fmap_type_sound_thm", ``
!H e.
  (birs_interpr_welltyped H) ==>
  (FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (birs_interpret_subst_fmap H e))
``,
  FULL_SIMP_TAC std_ss
    [birs_interpr_welltyped_def, birs_interpret_subst_fmap_def,
     FUN_FMAP_DEF, bir_vars_of_exp_FINITE, FEVERY_DEF] >>
  REPEAT STRIP_TAC >>
  CASE_TAC >> (REWRITE_TAC [type_of_bir_exp_def]) >>

  Cases_on `THE (symb_interpr_get H x)` >> (
    REWRITE_TAC [bir_val_to_constexp_def, type_of_bir_exp_def] >>
    METIS_TAC [type_of_bir_val_def]
  )
);

val birs_interpret_subst_EMPTY_vars_thm = store_thm(
   "birs_interpret_subst_EMPTY_vars_thm", ``
!H e e'.
  (bir_vars_of_exp e SUBSET symb_interpr_dom H) ==>
  (birs_interpret_subst H e = e') ==>
  (bir_vars_of_exp e' = EMPTY)
``,
  Induct_on `e` >- (
    FULL_SIMP_TAC std_ss [birs_interpret_subst_def, bir_exp_subst_def, bir_vars_of_exp_def]
  ) >- (
    FULL_SIMP_TAC std_ss [birs_interpret_subst_def, bir_exp_subst_def, bir_vars_of_exp_def]
  ) >- (
    (* BExp_Den *)
    FULL_SIMP_TAC std_ss [birs_interpret_subst_def, bir_exp_subst_def, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss
      [birs_interpret_subst_fmap_def, bir_exp_subst_var_def,
       bir_vars_of_exp_def, FINITE_SING, FLOOKUP_FUN_FMAP,
       SUBSET_DEF, IN_SING] >>

    REPEAT STRIP_TAC >>
    Cases_on `THE (symb_interpr_get H b)` >> (
      METIS_TAC [bir_val_to_constexp_def, bir_vars_of_exp_def]
    )
  ) >> (
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, birs_interpret_subst_def, bir_exp_subst_def, birs_interpret_subst_fmap_def, UNION_SUBSET, EMPTY_UNION] >>
    `FINITE (bir_vars_of_exp e ) /\
     FINITE (bir_vars_of_exp e') /\
     FINITE (bir_vars_of_exp e' UNION bir_vars_of_exp e'') /\
     FINITE (bir_vars_of_exp e  UNION bir_vars_of_exp e' ) /\
     FINITE (bir_vars_of_exp e  UNION bir_vars_of_exp e'')` by (
      METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION, UNION_COMM, UNION_ASSOC]
    ) >>
    REPEAT STRIP_TAC >> (
      METIS_TAC [bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm, UNION_COMM, UNION_ASSOC]
    )
  )
);

val birs_interpret_subst_type_sound_thm = store_thm(
   "birs_interpret_subst_type_sound_thm", ``
!H e e'.
  (birs_interpr_welltyped H) ==>
  (bir_vars_of_exp e SUBSET symb_interpr_dom H) ==>
  (birs_interpret_subst H e = e') ==>
  ((bir_vars_of_exp e' = EMPTY) /\
   (type_of_bir_exp e = type_of_bir_exp e'))
``,
  METIS_TAC
    [birs_interpret_subst_def,
     birs_interpret_subst_EMPTY_vars_thm,
     birs_interpret_subst_fmap_type_sound_thm,
     bir_exp_substitutionsTheory.bir_exp_subst_TYPE_EQ]
);

val birs_symb_typeof_exp_sound_thm = store_thm(
   "birs_symb_typeof_exp_sound_thm", ``
!prog.
  symb_typeof_exp_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss) [symb_typeof_exp_sound_def, birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_typeof_exp_sound_def, bir_symb_rec_sbir_def] >>

  METIS_TAC [birs_interpret_fun_def, birs_interpret_subst_type_sound_thm, bir_symb_supportTheory.bir_eval_exp_SOME_EQ_bir_exp_env_type_EMPTY_thm]
);


(*
=========================================================================
symb_mk_exp_eq_f_sound sr
=========================================================================
 *)

val birs_symb_mk_exp_eq_f_sound_thm = store_thm(
   "birs_symb_mk_exp_eq_f_sound_thm", ``
!prog.
  symb_mk_exp_eq_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_mk_exp_eq_f_sound_def, bir_symb_rec_sbir_def] >>
  cheat
);


(*
=========================================================================
symb_mk_exp_conj_f_sound sr
=========================================================================
 *)

val birs_symb_mk_exp_conj_f_sound_thm = store_thm(
   "birs_symb_mk_exp_conj_f_sound_thm", ``
!prog.
  symb_mk_exp_conj_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_mk_exp_conj_f_sound_def, bir_symb_rec_sbir_def] >>
  cheat
);


(*
=========================================================================
symb_mk_exp_symb_f_sound sr
=========================================================================
 *)

val birs_symb_mk_exp_symb_f_sound_thm = store_thm(
   "birs_symb_mk_exp_symb_f_sound_thm", ``
!prog.
  symb_mk_exp_symb_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_mk_exp_symb_f_sound_def, bir_symb_rec_sbir_def] >>
  cheat
);


(*
=========================================================================
symb_subst_f_sound sr
=========================================================================
 *)

val birs_symb_subst_f_sound_thm = store_thm(
   "birs_symb_subst_f_sound_thm", ``
!prog.
  symb_subst_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_subst_f_sound_def, bir_symb_rec_sbir_def] >>

  REPEAT STRIP_TAC >>
  cheat
);


(*
=========================================================================
symb_step_sound sr
=========================================================================
 *)


val birs_symb_matchstate_IMP_birs_state_set_failed_thm = store_thm(
   "birs_symb_matchstate_IMP_birs_state_set_failed_thm", ``
!sys H s.
  (birs_symb_matchstate sys H s) ==>
  (birs_symb_matchstate (birs_state_set_failed sys) H (bir_state_set_failed s))
``,
  SIMP_TAC (std_ss++birs_state_ss) [bir_state_set_failed_def, birs_state_set_failed_def, birs_symb_matchstate_def] >>

  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss++birs_state_ss) [birs_symb_symbols_def]
  )
);


val birs_symb_matchstate_IMP_same_pc_update_thm = store_thm(
   "birs_symb_matchstate_IMP_same_pc_update_thm", ``
!sys H s pc_upd.
  (birs_symb_matchstate sys H s) ==>
  (birs_symb_matchstate
     (sys with bsst_pc updated_by pc_upd)
     H
     (s with bst_pc updated_by pc_upd))
``,
  SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss++birs_state_ss) [birs_symb_symbols_def]
  )
);

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
    METIS_TAC [SUBSET_TRANS]
  ) >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [UNION_SUBSET, BIGUNION_SUBSET] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [] >>
  Cases_on `vn' = vn` >> (
    FULL_SIMP_TAC (std_ss) [UPDATE_APPLY, option_CLAUSES]
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
    FULL_SIMP_TAC (std_ss) [UPDATE_APPLY, option_CLAUSES, bir_env_lookup_def]
  )
);

val birs_eval_exp_IMP_varset_thm = store_thm(
   "birs_eval_exp_IMP_varset_thm", ``
!ex senv sv ty.
  (birs_eval_exp ex senv = SOME (sv,ty)) ==>
  (bir_vars_of_exp sv SUBSET (BIGUNION {bir_vars_of_exp e | (?vn. senv vn = SOME e)}))
``,
  Induct_on `ex` >> (
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_eval_exp_def, LET_DEF, birs_eval_exp_subst_def, bir_vars_of_exp_def]
  ) >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++PRED_SET_ss)
      [birs_senv_typecheck_thm, bir_envty_includes_vs_def, birs_envty_of_senv_def, birs_eval_exp_subst_var_def,
       bir_envty_includes_v_def, bir_vars_of_exp_def, BIGUNION, SUBSET_DEF] >>
    METIS_TAC []
  ) >> (
    REPEAT STRIP_TAC >> (
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>
      FULL_SIMP_TAC (std_ss)
        [birs_senv_typecheck_thm, bir_vars_of_exp_def, type_of_bir_exp_def, bir_envty_includes_vs_UNION] >>
      Cases_on `type_of_bir_exp ex` >> Cases_on `type_of_bir_exp ex'` >> Cases_on `type_of_bir_exp ex''` >> (
        FULL_SIMP_TAC (std_ss) [pair_CASE_def]
      )
    )
  ) >> (
    Cases_on `x` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [IS_SOME_EXISTS]
    )
  ) >>

  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [IS_SOME_EXISTS]
  )
);


(* ... *)

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
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>

    METIS_TAC [symb_interpr_for_symbs_EQ_set_typeerror_thm, birs_state_set_typeerror_def]
  ) >>

  FULL_SIMP_TAC (std_ss) [] >>
  `type_of_bir_val v' = ty` by (
    METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, birs_eval_exp_IMP_type_thm, option_CLAUSES]
  ) >>

  PAT_X_ASSUM ``birs_matchenv A B C`` (fn thm => (ASSUME_TAC ((Q.SPEC `bir_var_name v` o REWRITE_RULE [birs_matchenv_def]) thm) >> ASSUME_TAC thm)) >>

  (* does the environment have a value, and is it a value of the right type (and is the new value also of the right type)? *)
  FULL_SIMP_TAC (std_ss) [pair_CASE_def] >>
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
      METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, option_CLAUSES]
    ) >>

    PAT_X_ASSUM ``A \/ (?B. C /\ D)`` (K ALL_TAC) >>
    POP_ASSUM (fn thm => FULL_SIMP_TAC (std_ss) [thm]) >>

    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>
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

      METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, option_CLAUSES]
    ) >>

    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>

    CONJ_TAC >- (
      `bir_vars_of_exp sv SUBSET birs_symb_symbols sys` by (
        FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def] >>
        IMP_RES_TAC birs_eval_exp_IMP_varset_thm >>
        METIS_TAC [SUBSET_DEF, IN_UNION]
      ) >>
      METIS_TAC [symb_interpr_for_symbs_IMP_UPDATE_ENV_thm]
    ) >>

    Cases_on `s.bst_environ` >>
    FULL_SIMP_TAC (std_ss) [option_CLAUSES, bir_env_write_def, bir_env_update_def] >>
    METIS_TAC [birs_interpret_fun_IMP_birs_matchenv_thm]
  )
);

val birs_exec_stmt_assert_sound_thm = store_thm(
   "birs_exec_stmt_assert_sound_thm", ``
!ex s s' sys Pi H.
  (bir_exec_stmt_assert ex s = s') ==>
  (birs_exec_stmt_assert ex sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
);

val birs_exec_stmt_assume_sound_thm = store_thm(
   "birs_exec_stmt_assume_sound_thm", ``
!ex s s' sys Pi H.
  (bir_exec_stmt_assume ex s = s') ==>
  (birs_exec_stmt_assume ex sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
);

val birs_exec_stmt_observe_sound_thm = store_thm(
   "birs_exec_stmt_observe_sound_thm", ``
!oid ec el obf s s' sys Pi H.
  (SND (bir_exec_stmt_observe oid ec el obf s) = s') ==>
  (birs_exec_stmt_observe oid ec el obf sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  SIMP_TAC (std_ss++PRED_SET_ss)
    [bir_exec_stmt_observe_def, birs_exec_stmt_observe_def, LET_DEF] >>
  cheat
  (* TODO: this is wrong! *)
);

val birs_exec_stmtB_sound_thm = store_thm(
   "birs_exec_stmtB_sound_thm", ``
!stmt s s' sys Pi H.
  (SND (bir_exec_stmtB stmt s) = s') ==>
  (birs_exec_stmtB stmt sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  Cases_on `stmt` >> (
    REWRITE_TAC [bir_exec_stmtB_def, birs_exec_stmtB_def, birs_exec_stmt_assign_sound_thm, birs_exec_stmt_assert_sound_thm, birs_exec_stmt_assume_sound_thm, birs_exec_stmt_observe_sound_thm]
  )
);

(* ... *)

val birs_exec_stmt_halt_sound_thm = store_thm(
   "birs_exec_stmt_halt_sound_thm", ``
!ex s s' sys Pi H.
  (bir_exec_stmt_halt ex s = s') ==>
  (birs_exec_stmt_halt ex sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
  (* TODO: this is wrong! *)
);

val birs_exec_stmt_jmp_sound_thm = store_thm(
   "birs_exec_stmt_jmp_sound_thm", ``
!p le s s' sys Pi H.
  (bir_exec_stmt_jmp p le s = s') ==>
  (birs_exec_stmt_jmp p le sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
);

val birs_exec_stmt_cjmp_sound_thm = store_thm(
   "birs_exec_stmt_cjmp_sound_thm", ``
!p ex le1 le2 s s' sys Pi H.
  (bir_exec_stmt_cjmp p ex le1 le2 s = s') ==>
  (birs_exec_stmt_cjmp p ex le1 le2 sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  cheat
);

val birs_exec_stmtE_sound_thm = store_thm(
   "birs_exec_stmtE_sound_thm", ``
!p estmt s s' sys Pi H.
  (bir_exec_stmtE p estmt s = s') ==>
  (birs_exec_stmtE p estmt sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  Cases_on `estmt` >> (
    REWRITE_TAC [bir_exec_stmtE_def, birs_exec_stmtE_def, birs_exec_stmt_halt_sound_thm, birs_exec_stmt_jmp_sound_thm, birs_exec_stmt_cjmp_sound_thm]
  )
);

(* ... *)

val birs_exec_stmt_sound_thm = store_thm(
   "birs_exec_stmt_sound_thm", ``
!p stmt s s' sys Pi H.
  (SND (bir_exec_stmt p stmt s) = s') ==>
  (birs_exec_stmt p stmt sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  Cases_on `stmt` >> (
    REWRITE_TAC [bir_exec_stmt_def, birs_exec_stmt_def, birs_exec_stmtE_sound_thm]
  ) >>

  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [LET_DEF] >>
  REPEAT STRIP_TAC >>

  Cases_on `bir_exec_stmtB b s` >>
  rename1 `bir_exec_stmtB b s = (obs, s')` >>

  `SND (bir_exec_stmtB b s) = s'` by (
    FULL_SIMP_TAC (std_ss) []
  ) >>
  IMP_RES_TAC birs_exec_stmtB_sound_thm >>
  FULL_SIMP_TAC (std_ss) [] >>
  PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPECL [`sys`, `H`]) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>

  Ho_Rewrite.REWRITE_TAC [GSYM boolTheory.LEFT_EXISTS_AND_THM] >>
  Ho_Rewrite.ONCE_REWRITE_TAC [boolTheory.SWAP_EXISTS_THM] >>

  Q.EXISTS_TAC `sys'` >>
  FULL_SIMP_TAC (std_ss) [] >>

  `bir_state_is_terminated s' = birs_state_is_terminated sys'` by (
    METIS_TAC [birs_state_is_terminated_def, bir_state_is_terminated_def, birs_symb_matchstate_def]
  ) >>

  Cases_on `bir_state_is_terminated s'` >> (
    FULL_SIMP_TAC (std_ss) []
  ) >>

  METIS_TAC [birs_symb_matchstate_IMP_same_pc_update_thm]
);

val birs_exec_step_sound_thm = store_thm(
   "birs_exec_step_sound_thm", ``
!prog s s' sys Pi H.
  ((SND o bir_exec_step prog) s = s') ==>
  (birs_exec_step prog sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REWRITE_TAC [bir_exec_step_def, birs_exec_step_def, o_THM] >>
  REPEAT STRIP_TAC >>

  `bir_state_is_terminated s = birs_state_is_terminated sys` by (
    METIS_TAC [birs_state_is_terminated_def, bir_state_is_terminated_def, birs_symb_matchstate_def]
  ) >>

  Cases_on `bir_state_is_terminated s` >- (
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [IN_SING]
  ) >>

  `s.bst_pc = sys.bsst_pc` by (
    METIS_TAC [birs_symb_matchstate_def]
  ) >>

  FULL_SIMP_TAC (std_ss) [] >>
  Cases_on `bir_get_current_statement prog sys.bsst_pc` >- (
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [IN_SING, birs_symb_matchstate_IMP_birs_state_set_failed_thm]
  ) >>

  FULL_SIMP_TAC (std_ss) [] >>
  METIS_TAC [birs_exec_stmt_sound_thm]
);

(* ... *)

val birs_symb_step_sound_thm = store_thm(
   "birs_symb_step_sound_thm", ``
!prog.
  symb_step_sound (bir_symb_rec_sbir prog)
``,
  REWRITE_TAC [symb_step_sound_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `sys`) birs_symb_to_symbst_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `Pi`) birs_symb_to_symbst_SET_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [birs_symb_matchstate_EQ_thm] >>

  POP_ASSUM_LIST (ASSUME_TAC o LIST_CONJ o map (SIMP_RULE (std_ss++symb_TYPES_ss)
    [bir_symb_rec_sbir_def, birs_symb_to_from_symbst_thm, birs_symb_to_from_concst_thm])) >>
  FULL_SIMP_TAC std_ss [] >>

  `(SND o bir_exec_step prog) st' = st''` by (
    METIS_TAC [birs_symb_to_concst_BIJ_thm, o_DEF]
  ) >>
  `(birs_exec_step prog st) = Pi_t` by (
    METIS_TAC [birs_symb_to_symbst_BIJ_thm, IMAGE_11]
  ) >>

  IMP_RES_TAC birs_exec_step_sound_thm >>
  Q.EXISTS_TAC `birs_symb_to_symbst sys'` >>
  FULL_SIMP_TAC std_ss [birs_symb_matchstate_EQ_thm] >>

  METIS_TAC [IMAGE_IN]
);


val _ = export_theory();
