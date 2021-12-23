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
open bir_typing_expTheory;
open bir_expTheory;
open bir_exp_memTheory;
open bir_envTheory;
open bir_valuesTheory;
open bir_immTheory;

open symb_interpretTheory;
open bir_symbTheory;
open bir_symb_supportTheory;

open finite_mapTheory;
open pred_setTheory;
open optionTheory;
open pairTheory;

open HolBACoreSimps;
open symb_typesLib;



val _ = new_theory "bir_symb_sound_core";

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val birs_symb_symbols_def = Define `
    birs_symb_symbols sys =
      (BIGUNION {bir_vars_of_exp e | ?vn. sys.bsst_environ vn = SOME e}) UNION (bir_vars_of_exp sys.bsst_pcond)
`;

val birs_symb_symbols_EQ_thm = store_thm(
   "birs_symb_symbols_EQ_thm", ``
!prog sys. symb_symbols (bir_symb_rec_sbir prog) (birs_symb_to_symbst sys) = birs_symb_symbols sys
``,
  Cases_on `sys` >>
  SIMP_TAC (std_ss++symb_TYPES_ss)
    [symb_symbols_def, bir_symb_rec_sbir_def, symb_symbols_store_def,
     symb_symbst_pcond_def, birs_symb_symbols_def] >>

  SIMP_TAC (std_ss++birs_state_ss) [birs_symb_to_symbst_def, symb_symbst_pcond_def, symb_symbst_store_def]
);

val birs_interpr_welltyped_def = Define `
    birs_interpr_welltyped H =
      !sy. sy IN (symb_interpr_dom H) ==> type_of_bir_val (THE (symb_interpr_get H sy)) = bir_var_type sy
`;

val birs_interpr_welltyped_EQ_thm = store_thm(
   "birs_interpr_welltyped_EQ_thm", ``
!prog H.
symb_interpr_welltyped (bir_symb_rec_sbir prog) H = birs_interpr_welltyped H
``,
  SIMP_TAC (std_ss)
    [symb_interpr_welltyped_def, birs_interpr_welltyped_def] >>
  SIMP_TAC (std_ss++symb_TYPES_ss)
    [bir_symb_rec_sbir_def] >>

  METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, option_CLAUSES]
);

val birs_interpret_fun_EQ_thm = store_thm(
   "birs_interpret_fun_EQ_thm", ``
!prog H e vo.
((bir_symb_rec_sbir prog).sr_interpret_f H e = vo)
<=>
(birs_interpret_fun H e = vo)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss)
    [bir_symb_rec_sbir_def]
);

val birs_matchenv_def = Define `
    birs_matchenv H senv env =
      (!var. (bir_env_lookup var env <> NONE \/ senv var <> NONE) ==>
         ?e v.
            senv   var = SOME e /\
            bir_env_lookup var env = SOME v /\
            birs_interpret_fun H e = SOME v)
`;

val birs_matchenv_EQ_thm = store_thm(
   "birs_matchenv_EQ_thm", ``
!prog H f s.
symb_interpr_symbstore (bir_symb_rec_sbir prog) H f
       (symb_concst_store (birs_symb_to_concst s)) =
  birs_matchenv H f s.bst_environ
``,
  Cases_on `s` >>
  SIMP_TAC (std_ss++holBACore_ss)
    [symb_interpr_symbstore_def, birs_matchenv_def, symb_concst_store_def, birs_symb_to_concst_def] >>
  SIMP_TAC (std_ss++symb_TYPES_ss)
    [bir_symb_rec_sbir_def] >>

  METIS_TAC []
);

val birs_symb_matchstate_def = Define `
    birs_symb_matchstate sys H s = (
      (symb_interpr_for_symbs (birs_symb_symbols sys) H) /\
      (birs_interpr_welltyped H) /\
      (sys.bsst_pc = s.bst_pc) /\
      (birs_matchenv H sys.bsst_environ s.bst_environ) /\
      (birs_interpret_fun H sys.bsst_pcond = SOME bir_val_true) /\
      (sys.bsst_status = s.bst_status))
`;

val birs_symb_matchstate_EQ_thm = store_thm(
   "birs_symb_matchstate_EQ_thm", ``
!prog sys H s.
symb_matchstate (bir_symb_rec_sbir prog) (birs_symb_to_symbst sys) H (birs_symb_to_concst s) =
  birs_symb_matchstate sys H s
``,
  Cases_on `sys` >>

  SIMP_TAC (std_ss)
    [symb_matchstate_def, symb_suitable_interpretation_def, birs_symb_symbols_EQ_thm, birs_matchenv_EQ_thm, birs_interpr_welltyped_EQ_thm] >>

  SIMP_TAC (std_ss++birs_state_ss)
    [birs_symb_to_symbst_def, birs_symb_matchstate_def] >>

  SIMP_TAC (std_ss)
    [symb_symbst_pc_def, symb_symbst_extra_def, symb_symbst_store_def, symb_interpr_symbpcond_def, symb_symbst_pcond_def, birs_interpret_fun_EQ_thm] >>

  SIMP_TAC (std_ss++symb_TYPES_ss)
    [bir_symb_rec_sbir_def] >>

  Cases_on `s` >>
  SIMP_TAC (std_ss++holBACore_ss)
    [symb_concst_pc_def, birs_symb_to_concst_def, symb_concst_store_def, symb_concst_extra_def]
);

val birs_interpret_subst_PRESERVES_type_thm = store_thm(
   "birs_interpret_subst_PRESERVES_type_thm", ``
!sv H.
  (birs_interpr_welltyped H) ==>
  (type_of_bir_exp (birs_interpret_subst H sv) = type_of_bir_exp sv)
``,
  REWRITE_TAC [birs_interpret_subst_def, birs_interpret_subst_fmap_def] >>
  REPEAT STRIP_TAC >>

  MATCH_MP_TAC bir_exp_subst_TYPE_EQ >>

  FULL_SIMP_TAC std_ss [FEVERY_DEF, FUN_FMAP_DEF, bir_vars_of_exp_FINITE, birs_interpret_subst_fmap_get_def] >>
  REPEAT STRIP_TAC >>
  CASE_TAC >> (
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def]
  ) >>

  FULL_SIMP_TAC std_ss [birs_interpr_welltyped_def] >>
  Cases_on `THE (symb_interpr_get H x)` >> (
    FULL_SIMP_TAC std_ss [bir_val_to_constexp_def, type_of_bir_exp_def] >>
    METIS_TAC [type_of_bir_val_def]
  )
);

val birs_interpret_fun_PRESERVES_type_thm = store_thm(
   "birs_interpret_fun_PRESERVES_type_thm", ``
!sv H v.
  (birs_interpr_welltyped H) ==>
  (birs_interpret_fun H sv = SOME v) ==>
  (type_of_bir_exp sv = SOME (type_of_bir_val v))
``,
  REWRITE_TAC [birs_interpret_fun_def] >>
  REPEAT STRIP_TAC >>

  `type_of_bir_exp (birs_interpret_subst H sv) = type_of_bir_exp sv` by (
    METIS_TAC [birs_interpret_subst_PRESERVES_type_thm]
  ) >>

  METIS_TAC [bir_eval_exp_IS_SOME_IMPLIES_TYPE]
);

val birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm = store_thm(
   "birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm", ``
!H senv env vs.
  (birs_interpr_welltyped H) ==>
  (birs_matchenv H senv env) ==>
  (bir_envty_includes_vs (birs_envty_of_senv senv) vs
   <=>
   bir_envty_includes_vs (bir_envty_of_env env) vs)
``,
  Cases_on `env` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, bir_envty_includes_v_def, birs_envty_of_senv_def, bir_envty_of_env_def, birs_matchenv_def, bir_env_lookup_def] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    (PAT_X_ASSUM ``!x. v IN vs ==> B`` (ASSUME_TAC o Q.SPEC `v`)) >>
    (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `(bir_var_name v)`)) >>

    METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, option_CLAUSES]
  )
);

val birs_interpret_fun_sound_NONE_thm = store_thm(
   "birs_interpret_fun_sound_NONE_thm", ``
!H senv env e.
  (birs_interpr_welltyped H) ==>
  (birs_matchenv H senv env) ==>
  (birs_eval_exp e senv = NONE) ==>
  (bir_eval_exp e env = NONE)
``,
  METIS_TAC
    [birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm,
     bir_eval_exp_NONE_EQ_bir_exp_env_type_thm,
     birs_eval_exp_NONE_EQ_bir_exp_env_type_thm]
);


val birs_interpret_fun_sound_thm = store_thm(
   "birs_interpret_fun_sound_thm", ``
!H senv env e sv ty v.
  (birs_interpr_welltyped H) ==>
  (birs_matchenv H senv env) ==>
  (birs_eval_exp e senv = SOME (sv, ty)) ==>
  (?v. birs_interpret_fun H sv = SOME v /\ bir_eval_exp e env = SOME v)
``,
  Induct_on `e` >- (
    (* BExp_Const *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def, birs_interpret_fun_def, birs_interpret_subst_def] >>
    METIS_TAC [bir_exp_subst_def, bir_eval_exp_def]
  ) >- (
    (* BExp_MemConst *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def, birs_interpret_fun_def, birs_interpret_subst_def] >>
    METIS_TAC [bir_exp_subst_def, bir_eval_exp_def]
  ) >- (
    (* BExp_Den *)
    REPEAT STRIP_TAC >>
    IMP_RES_TAC birs_eval_exp_IMP_type_thm >>

    FULL_SIMP_TAC std_ss
      [birs_eval_exp_def, LET_DEF, birs_senv_typecheck_thm, bir_vars_of_exp_def, bir_envty_includes_vs_def, IN_SING] >>

    Cases_on `birs_envty_of_senv senv` >>
    FULL_SIMP_TAC std_ss
      [bir_envty_includes_v_def, birs_eval_exp_subst_def, birs_eval_exp_subst_var_def] >>
    Cases_on `senv (bir_var_name b)` >- (
      FULL_SIMP_TAC std_ss [birs_envty_of_senv_def, bir_var_environment_typing_t_11] >>

      `f (bir_var_name b) = NONE` by (
        PAT_X_ASSUM ``A o B = C`` (fn thm => REWRITE_TAC [GSYM thm]) >>
        ASM_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    Cases_on `env` >>
    FULL_SIMP_TAC std_ss [option_CLAUSES, type_of_bir_exp_def, bir_eval_exp_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def] >>

    FULL_SIMP_TAC std_ss [birs_matchenv_def] >>
    PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `bir_var_name b`) >>
    REV_FULL_SIMP_TAC std_ss [option_CLAUSES] >>

    METIS_TAC [option_CLAUSES, birs_interpret_fun_PRESERVES_type_thm]
  ) >- (
    (* BExp_Cast *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    `type_of_bir_val v = x` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    Cases_on `v` >> (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def] >>
      METIS_TAC [bir_type_t_distinct, bir_eval_cast_def]
    )
  ) >- (
    (* BExp_UnaryExp *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    `type_of_bir_val v = x` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    Cases_on `v` >> (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def] >>
      METIS_TAC [bir_type_t_distinct, bir_eval_unary_exp_def]
    )
  ) >- (
    (* BExp_BinExp *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [Once UNION_COMM, bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = x'` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>
    `type_of_bir_val v' = x` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    Cases_on `v` >> Cases_on `v'` >> (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def] >>
      METIS_TAC [bir_type_t_distinct, bir_type_t_11, bir_eval_bin_exp_def]
    )
  ) >- (
    (* BExp_BinPred *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [Once UNION_COMM, bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = x'` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>
    `type_of_bir_val v' = x` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    Cases_on `v` >> Cases_on `v'` >> (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def] >>
      METIS_TAC [bir_type_t_distinct, bir_type_t_11, bir_eval_bin_pred_def]
    )
  ) >- (
    (* BExp_MemEq *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >> (
      Cases_on `x` >> (
        REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
      )
    ) >>
    Cases_on `x'` >> (
      REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
    ) >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [Once UNION_COMM, bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = BType_Mem b' b0'` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>
    `type_of_bir_val v' = BType_Mem b b0` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    Cases_on `v` >> Cases_on `v'` >> (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def] >>
      METIS_TAC [bir_type_t_distinct, bir_type_t_11, bir_eval_memeq_def]
    )
  ) >- (
    (* BExp_IfThenElse *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e''` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [prove(
      ``FINITE(bir_vars_of_exp sv'' UNION bir_vars_of_exp sv')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [prove(
      ``bir_vars_of_exp sv'' UNION bir_vars_of_exp sv' UNION bir_vars_of_exp sv
        = bir_vars_of_exp sv UNION bir_vars_of_exp sv'' UNION bir_vars_of_exp sv'``, METIS_TAC [UNION_COMM, UNION_ASSOC]),
      prove(
      ``FINITE(bir_vars_of_exp sv UNION bir_vars_of_exp sv'')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [prove(
      ``bir_vars_of_exp sv UNION bir_vars_of_exp sv'' UNION bir_vars_of_exp sv'
        = bir_vars_of_exp sv UNION bir_vars_of_exp sv' UNION bir_vars_of_exp sv''``, METIS_TAC [UNION_COMM, UNION_ASSOC]),       prove(
      ``FINITE(bir_vars_of_exp sv UNION bir_vars_of_exp sv')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = x'' /\ type_of_bir_val v' = x' /\ type_of_bir_val v'' = x` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def, BType_Bool_def, bir_type_t_11] >>
    `type_of_bir_val v = type_of_bir_val v'` by ASM_REWRITE_TAC [] >>
    PAT_X_ASSUM ``A = BType_Imm Bit1`` (ASSUME_TAC) >>
    FULL_SIMP_TAC std_ss [] >>

    Cases_on `v''` >> (
      FULL_SIMP_TAC std_ss [type_of_bir_val_def, bir_type_t_distinct]
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC std_ss [type_of_bir_imm_def, bir_type_t_11, bir_immtype_t_distinct]
    ) >>

    SIMP_TAC std_ss [bir_eval_ifthenelse_def] >>
    METIS_TAC []
  ) >- (
    (* BExp_Load *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >> (
      Cases_on `x` >> (
        REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
      )
    ) >>
    Cases_on `x'` >> (
      REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
    ) >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [bir_vars_of_exp_FINITE, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [prove(
      ``bir_vars_of_exp sv' UNION bir_vars_of_exp sv
        = bir_vars_of_exp sv UNION bir_vars_of_exp sv'``, METIS_TAC [UNION_COMM, UNION_ASSOC]),
      bir_vars_of_exp_FINITE,
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = BType_Imm b' /\ type_of_bir_val v' = BType_Mem b b0` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def, BType_Bool_def, bir_type_t_11] >>

    Cases_on `v` >> Cases_on `v'` >> (
      FULL_SIMP_TAC std_ss [type_of_bir_val_def, bir_type_t_distinct]
    ) >>

    SIMP_TAC std_ss [bir_eval_load_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    IMP_RES_TAC bir_load_from_mem_IS_SOME_thm >>
    CASE_TAC >>
    METIS_TAC [option_CLAUSES]
  ) >> (
    (* BExp_Store *)
    SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_vars_of_exp_def] >>
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
    FULL_SIMP_TAC std_ss [pair_CASE_def] >>
    Cases_on `type_of_bir_exp e` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e''` >> (
      REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
    ) >> (
      Cases_on `x` >> (
        REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
      )
    ) >> (
      Cases_on `x'` >> (
        REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
      )
    ) >>
    Cases_on `x''` >> (
      REV_FULL_SIMP_TAC std_ss [bir_type_t_case_def]
    ) >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_t_case_def, IS_SOME_EXISTS] >>

    FULL_SIMP_TAC std_ss [bir_envty_includes_vs_UNION] >>
    IMP_RES_TAC birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, bir_eval_exp_def, birs_eval_exp_subst_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_eval_exp_def, bir_vars_of_exp_def, bir_exp_subst_def] >>

    SIMP_TAC std_ss [prove(
      ``FINITE(bir_vars_of_exp sv'' UNION bir_vars_of_exp sv')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [prove(
      ``bir_vars_of_exp sv'' UNION bir_vars_of_exp sv' UNION bir_vars_of_exp sv
        = bir_vars_of_exp sv UNION bir_vars_of_exp sv'' UNION bir_vars_of_exp sv'``, METIS_TAC [UNION_COMM, UNION_ASSOC]),
      prove(
      ``FINITE(bir_vars_of_exp sv UNION bir_vars_of_exp sv'')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    SIMP_TAC std_ss [prove(
      ``bir_vars_of_exp sv UNION bir_vars_of_exp sv'' UNION bir_vars_of_exp sv'
        = bir_vars_of_exp sv UNION bir_vars_of_exp sv' UNION bir_vars_of_exp sv''``, METIS_TAC [UNION_COMM, UNION_ASSOC]),       prove(
      ``FINITE(bir_vars_of_exp sv UNION bir_vars_of_exp sv')``, METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION]),
      bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm] >>
    ASM_SIMP_TAC std_ss [] >>

    `type_of_bir_val v = BType_Imm b'' /\ type_of_bir_val v' = BType_Imm b' /\ type_of_bir_val v'' = BType_Mem b' b0` by (
      METIS_TAC [option_CLAUSES, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, bir_eval_exp_SOME_EQ_bir_exp_env_type_thm]
    ) >>

    FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, type_of_bir_val_def, bir_type_is_Imm_def, bir_eval_bin_exp_def, BType_Bool_def, bir_type_t_11] >>

    Cases_on `v` >> Cases_on `v'` >> Cases_on `v''` >> (
      FULL_SIMP_TAC std_ss [type_of_bir_val_def, bir_type_t_distinct]
    ) >>

    SIMP_TAC std_ss [bir_eval_store_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    IMP_RES_TAC bir_store_in_mem_IS_SOME_thm >>
    CASE_TAC >>
    METIS_TAC [option_CLAUSES]
  )
);

val birs_eval_exp_sound_thm = store_thm(
   "birs_eval_exp_sound_thm", ``
!H senv env e.
  (birs_interpr_welltyped H) ==>
  (birs_matchenv H senv env) ==>
  ((birs_eval_exp e senv = NONE /\ bir_eval_exp e env = NONE) \/
   (?sv ty v.
      birs_eval_exp e senv = SOME (sv, ty) /\ bir_eval_exp e env = SOME v /\
      birs_interpret_fun H sv = SOME v))
``,
  REPEAT STRIP_TAC >>

  Cases_on `birs_eval_exp e senv = NONE` >- (
    METIS_TAC [bir_eval_exp_NONE_EQ_bir_exp_env_type_thm, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm, birs_eval_exp_NONE_EQ_bir_exp_env_type_thm]
  ) >>

  `IS_SOME (birs_eval_exp e senv)` by (
    METIS_TAC [NOT_IS_SOME_EQ_NONE]
  ) >>
  FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] >>
  Cases_on `x` >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC (GSYM birs_eval_exp_SOME_EQ_bir_exp_env_type_thm) >>

  `?v. bir_eval_exp e env = SOME v` by (
    METIS_TAC [bir_eval_exp_SOME_EQ_bir_exp_env_type_thm, birs_matchenv_IMP_EQ_bir_envty_includes_vs_thm]
  ) >>

  METIS_TAC [birs_interpret_fun_sound_thm]
);

val symb_interpr_for_symbs_EQ_set_typeerror_thm = store_thm(
   "symb_interpr_for_symbs_EQ_set_typeerror_thm", ``
!sys H.
  (symb_interpr_for_symbs (birs_symb_symbols (birs_state_set_typeerror sys)) H) =
  (symb_interpr_for_symbs (birs_symb_symbols sys) H)
``,
  SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def, birs_symb_symbols_def]
);


val _ = export_theory();
