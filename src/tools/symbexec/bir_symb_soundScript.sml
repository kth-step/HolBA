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
open bir_symb_supportTheory;
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
  FULL_SIMP_TAC std_ss [birs_interpret_subst_fmap_get_def] >>

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
     FUN_FMAP_DEF, bir_vars_of_exp_FINITE, FEVERY_DEF,
     birs_interpret_subst_fmap_get_def] >>
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
       SUBSET_DEF, IN_SING, birs_interpret_subst_fmap_get_def] >>

    REPEAT STRIP_TAC >>
    Cases_on `THE (symb_interpr_get H b)` >> (
      METIS_TAC [bir_val_to_constexp_def, bir_vars_of_exp_def]
    )
  ) >> (
    FULL_SIMP_TAC std_ss
      [bir_vars_of_exp_def, birs_interpret_subst_def, bir_exp_subst_def,
       birs_interpret_subst_fmap_def, UNION_SUBSET, EMPTY_UNION,
       birs_interpret_subst_fmap_get_def] >>
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
symb_val_eq_sound sr
=========================================================================
 *)

val birs_symb_val_eq_sound_thm = store_thm(
   "birs_symb_val_eq_sound_thm", ``
!prog.
  symb_val_eq_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss) [symb_val_eq_sound_def] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def] >>

  GEN_TAC >>
  Cases_on `v` >> (
    SIMP_TAC (std_ss++holBACore_ss)
      [birs_val_eq_def, bir_eval_bin_pred_def, bir_val_true_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR]
  ) >>

  SIMP_TAC (std_ss) [bir_exp_memTheory.bir_memeq_def]
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
  SIMP_TAC (std_ss) [symb_mk_exp_eq_f_sound_def, birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def] >>
  CONJ_TAC >- (
    (* interpretation *)
    REPEAT STRIP_TAC >>
    (* if the first expression interprets to nothing *)
    Cases_on `type_of_bir_exp e1` >- (
      FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

      Cases_on `birs_interpret_fun_ALT H e1` >- (
        FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_pred_def]
      ) >>
      METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, option_CLAUSES, birs_interpret_fun_thm]
    ) >>

    FULL_SIMP_TAC std_ss [option_CLAUSES] >>
    Cases_on `x` >- (
      (* compare Imm *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

      Cases_on `birs_interpret_fun_ALT H e1` >> Cases_on `birs_interpret_fun_ALT H e2` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_pred_def, bir_eval_memeq_def]
      ) >> (
        Cases_on `x` >> (
          FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_pred_def, bir_eval_memeq_def]
        )
      ) >- (
        Cases_on `x'` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, bir_eval_bin_pred_def, birs_val_eq_def]
        )
      ) >>
      (* type error (compare Imm and Mem) *)
      METIS_TAC
        [birs_interpret_fun_PRESERVES_type_thm, type_of_bir_val_def,
         birs_interpret_fun_thm, bir_valuesTheory.bir_type_t_distinct, option_CLAUSES]
    ) >>

    (* compare Mem *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

    Cases_on `birs_interpret_fun_ALT H e1` >> Cases_on `birs_interpret_fun_ALT H e2` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_pred_def, bir_eval_memeq_def]
    ) >> (
      Cases_on `x` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_pred_def, bir_eval_memeq_def]
      )
    ) >- (
      (* type error (compare Imm and Mem) *)
      METIS_TAC
        [birs_interpret_fun_PRESERVES_type_thm, type_of_bir_val_def,
         birs_interpret_fun_thm, bir_valuesTheory.bir_type_t_distinct, option_CLAUSES]
    ) >>

    Cases_on `x'` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, bir_eval_bin_pred_def, birs_val_eq_def]
    )
  ) >>

  (* variable set *)
  REPEAT STRIP_TAC >>
  Cases_on `type_of_bir_exp e1` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES]
  ) >>

  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES]
  )
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
  SIMP_TAC (std_ss) [symb_mk_exp_conj_f_sound_def, birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def] >>
  CONJ_TAC >- (
    (* interpretation *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

    Cases_on `birs_interpret_fun_ALT H e1` >> Cases_on `birs_interpret_fun_ALT H e2` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_exp_def]
    ) >> (
      Cases_on `x` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES, bir_eval_bin_exp_def]
      )
    ) >- (
      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, bir_eval_bin_exp_def, bir_val_true_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_exp_REWRS] >>
        wordsLib.WORD_DECIDE_TAC
      )
    ) >>
    (* type error (true is no Mem) *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def]
  ) >>

  (* variable set *)
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES]
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
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_mk_exp_symb_f_sound_def, bir_symb_rec_sbir_def, bir_vars_of_exp_def] >>
  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, birs_interpret_get_var_def] >>
  METIS_TAC [symb_interpr_dom_thm, option_CLAUSES]
);


(*
=========================================================================
symb_subst_f_sound sr
=========================================================================
 *)

val birs_interpret_fun_bir_exp_subst1_interpr_update_sound_thm = store_thm(
   "birs_interpret_fun_bir_exp_subst1_interpr_update_sound_thm", ``
!H v symb symb_inst e.
  (type_of_bir_exp symb_inst = SOME (bir_var_type symb)) ==>
  (birs_interpret_fun H symb_inst = SOME v) ==>
  (birs_interpret_fun H (bir_exp_subst1 symb symb_inst e) =
   birs_interpret_fun (symb_interpr_update H (symb,SOME v)) e)
``,
  Induct_on `e` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, bir_exp_subst1_def, bir_exp_subst_def]
  ) >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, bir_exp_subst1_def, bir_exp_subst_def]
  ) >- (
    (* BExp_Den *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, bir_exp_subst1_def, bir_exp_subst_def, bir_exp_subst_var_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
    REPEAT STRIP_TAC >>

    Cases_on `symb = b` >> Cases_on `b IN symb_interpr_dom H` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, bir_exp_subst1_def, bir_exp_subst_def, bir_exp_subst_var_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_get_var_def, symb_interpr_dom_UPDATE_SOME_thm, IN_INSERT, symb_interpr_get_update_thm]
    )
  ) >> (
    REPEAT STRIP_TAC >>
    SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_thm, birs_interpret_fun_ALT_def, bir_exp_subst1_def, bir_exp_subst_def] >>
    REWRITE_TAC [GSYM birs_interpret_fun_thm, GSYM bir_exp_subst1_def] >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (IMP_RES_TAC)) >>
    METIS_TAC []
  )
);

val birs_symb_subst_f_sound_thm = store_thm(
   "birs_symb_subst_f_sound_thm", ``
!prog.
  symb_subst_f_sound (bir_symb_rec_sbir prog)
``,
  SIMP_TAC (std_ss++symb_TYPES_ss) [symb_subst_f_sound_def, bir_symb_rec_sbir_def] >>
  REPEAT STRIP_TAC >- (
    (* interpretation *)
    METIS_TAC [birs_interpret_fun_bir_exp_subst1_interpr_update_sound_thm]
  ) >>

  (* variable set *)
  METIS_TAC [bir_exp_subst1_USED_VARS]
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

val birs_state_set_typeerror_SING_symb_matchstate_thm = store_thm(
   "birs_state_set_typeerror_SING_symb_matchstate_thm", ``
!s sys s' Pi H.
  (bir_state_set_typeerror s = s') ==>
  ({birs_state_set_typeerror sys} = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
  PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_symb_matchstate_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [birs_state_set_typeerror_def, bir_state_set_typeerror_def] >>
  METIS_TAC [symb_interpr_for_symbs_EQ_set_typeerror_thm, birs_state_set_typeerror_def]
);

val birs_symb_matchstate_IMP_bir_symb_eval_exp_thm = store_thm(
   "birs_symb_matchstate_IMP_bir_symb_eval_exp_thm", ``
!s sys H e.
  (birs_symb_matchstate sys H s) ==>
  ((birs_eval_exp e sys.bsst_environ = NONE /\
    bir_eval_exp e s.bst_environ = NONE)
   \/
   (?sv ty v.
         birs_eval_exp e sys.bsst_environ = SOME (sv,ty) /\
         bir_eval_exp e s.bst_environ = SOME v /\
         birs_interpret_fun H sv = SOME v /\
         type_of_bir_val v = ty))
``,
  REPEAT STRIP_TAC >>

  Cases_on `birs_eval_exp e sys.bsst_environ` >- (
    METIS_TAC [birs_symb_matchstate_def, birs_eval_exp_sound_thm, option_CLAUSES]
  ) >>

  FULL_SIMP_TAC std_ss [birs_symb_matchstate_def] >>
  Cases_on `x` >>

  IMP_RES_TAC birs_eval_exp_sound_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `e`) >>
  REV_FULL_SIMP_TAC (std_ss) [option_CLAUSES] >>

  METIS_TAC [birs_interpret_fun_PRESERVES_type_thm, birs_eval_exp_IMP_type_thm, option_CLAUSES]
);

val birs_symb_matchstate_IMP_bir_symb_eval_exp_SOME_thm = store_thm(
   "birs_symb_matchstate_IMP_bir_symb_eval_exp_SOME_thm", ``
!s sys H e sv ty.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_exp e sys.bsst_environ = SOME (sv,ty)) ==>
  (?v. (bir_eval_exp e s.bst_environ = SOME v) /\
       (birs_interpret_fun H sv = SOME v) /\
       (type_of_bir_val v = ty))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `e`) >>

  REV_FULL_SIMP_TAC std_ss [option_CLAUSES]
);

val birs_symb_matchstate_IMP_bir_symb_eval_exp_NONE_thm = store_thm(
   "birs_symb_matchstate_IMP_bir_symb_eval_exp_NONE_thm", ``
!s sys H e.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_exp e sys.bsst_environ = NONE) ==>
  (bir_eval_exp e s.bst_environ = NONE)
``,
  METIS_TAC [birs_symb_matchstate_IMP_bir_symb_eval_exp_thm, option_CLAUSES]
);


val symb_interpr_for_symbs_COND_thm = store_thm(
   "symb_interpr_for_symbs_COND_thm", ``
!sys sys' H e sv ty.
  (birs_eval_exp e sys.bsst_environ = SOME (sv, ty)) ==>
  (symb_interpr_for_symbs (birs_symb_symbols sys) H) ==>
  (symb_interpr_for_symbs (birs_symb_symbols sys') H) ==>
  ((symb_interpr_for_symbs
          (birs_symb_symbols
             (sys' with bsst_pcond := BExp_BinExp BIExp_And sys.bsst_pcond sv))
          H)
   /\
   (symb_interpr_for_symbs
          (birs_symb_symbols
             (sys' with
                bsst_pcond :=
                  BExp_BinExp BIExp_And sys.bsst_pcond
                    (BExp_UnaryExp BIExp_Not sv))) H))
``,
  FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_for_symbs_def, birs_symb_symbols_def] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss) [UNION_SUBSET, bir_vars_of_exp_def] >>
    REPEAT STRIP_TAC >>

    METIS_TAC [bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm, SUBSET_TRANS]
  )
);

val symb_interpr_for_symbs_UPD_status_thm = store_thm(
   "symb_interpr_for_symbs_UPD_status_thm", ``
!sys H status.
  (symb_interpr_for_symbs (birs_symb_symbols sys) H) ==>
  (symb_interpr_for_symbs (birs_symb_symbols
            (sys with bsst_status := status)) H)
``,
  FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_for_symbs_def, birs_symb_symbols_def]
);

val birs_branch_def = Define `
   (birs_branch T sv sys =
      sys with bsst_pcond := BExp_BinExp BIExp_And sys.bsst_pcond sv) /\
   (birs_branch F sv sys =
      sys with bsst_pcond := BExp_BinExp BIExp_And sys.bsst_pcond (BExp_UnaryExp BIExp_Not sv))
`;

(* TODO: want to introduce definition for a triple (eval, seval, interpr)? *)
val birs_symb_matchstate_COND_UNION_thm = store_thm(
   "birs_symb_matchstate_COND_UNION_thm", ``
!s sys H e sv bv stfun sffun systfun sysffun s' Pi.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_exp e sys.bsst_environ = SOME (sv,BType_Imm Bit1)) ==>
  (bir_eval_exp e s.bst_environ = SOME (BVal_Imm (Imm1 (bool2w bv)))) ==>
  (birs_interpret_fun H sv = bir_eval_exp e s.bst_environ) ==>

  (if bv then
     birs_symb_matchonestate (systfun (birs_branch T sv sys)) H (stfun s)
   else
     birs_symb_matchonestate (sysffun (birs_branch F sv sys)) H (sffun s)) ==>

  ((if bv then stfun s else sffun s) = s') ==>
  ((systfun (birs_branch T sv sys)) UNION
   (sysffun (birs_branch F sv sys))
   = Pi) ==>

  (birs_symb_matchonestate Pi H s')
``,
  REWRITE_TAC [birs_symb_matchonestate_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `bv` >> (
    FULL_SIMP_TAC (std_ss) [] >>
    rename1 `sysx ∈ sysxfun (birs_branch bv sv sys)` >>
    Q.EXISTS_TAC `sysx` >>

    CONJ_TAC >- (
      METIS_TAC [IN_UNION, IN_IMAGE, IN_DEF]
    ) >>

    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_symb_matchstate_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) []
  )
);

(*
    CONJ_TAC >- (
      METIS_TAC [symb_interpr_for_symbs_COND_thm]
    )
  ) >> (
    REV_FULL_SIMP_TAC (std_ss) [GSYM bir_val_true_def] >>

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def, bir_immTheory.bool2w_def] >>
    wordsLib.WORD_DECIDE_TAC
  )
);
*)


val birs_symb_matchstate_COND_thm = store_thm(
   "birs_symb_matchstate_COND_thm", ``
!s sys H e sv bv st sf syst sysf s' Pi.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_exp e sys.bsst_environ = SOME (sv,BType_Imm Bit1)) ==>
  (bir_eval_exp e s.bst_environ = SOME (BVal_Imm (Imm1 (bool2w bv)))) ==>
  (birs_interpret_fun H sv = bir_eval_exp e s.bst_environ) ==>
  (birs_symb_matchstate syst H st) ==>
  (birs_symb_matchstate sysf H sf) ==>
  ((if bv then st else sf) = s') ==>
  ({syst with bsst_pcond := BExp_BinExp BIExp_And sys.bsst_pcond sv;
         sysf with
           bsst_pcond :=
             BExp_BinExp BIExp_And sys.bsst_pcond
               (BExp_UnaryExp BIExp_Not sv)} = Pi) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>
  Cases_on `bv` >> (
    FULL_SIMP_TAC (std_ss) []
  ) >| [
    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (fn thm => (ASSUME_TAC thm >> ((EXISTS_TAC o hd o pred_setSyntax.strip_set o fst o dest_eq o concl) thm)))
    ,
    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (fn thm => (ASSUME_TAC thm >> ((EXISTS_TAC o hd o tl o pred_setSyntax.strip_set o fst o dest_eq o concl) thm)))
  ] >> (
    PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_symb_matchstate_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [] >>

    CONJ_TAC >- (
      METIS_TAC [symb_interpr_for_symbs_COND_thm]
    )
  ) >> (
    REV_FULL_SIMP_TAC (std_ss) [GSYM bir_val_true_def] >>

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def, bir_immTheory.bool2w_def] >>
    wordsLib.WORD_DECIDE_TAC
  )
);

val birs_symb_matchstate_UPD_status_thm = store_thm(
   "birs_symb_matchstate_UPD_status_thm", ``
!status s sys H s' Pi.
  (birs_symb_matchstate sys H s) ==>
  ((s with bst_status := status) = s') ==>
  ({sys with bsst_status := status} = Pi) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
  PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_symb_matchstate_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [] >>

  METIS_TAC [symb_interpr_for_symbs_UPD_status_thm]
);

val bir_eval_exp_BOOL_NONE_sound_thm = store_thm(
   "bir_eval_exp_BOOL_NONE_sound_thm", ``
!s sys H e.
  (birs_symb_matchstate sys H s) ==>
  (option_CASE (bir_eval_exp e s.bst_environ) NONE bir_dest_bool_val = NONE) ==>
  ((birs_eval_exp e sys.bsst_environ = NONE) \/
   (?sv. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit8)) \/
   (?sv. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit16)) \/
   (?sv. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit32)) \/
   (?sv. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit64)) \/
   (?sv. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit128)) \/
   (?sv aty vty. birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Mem aty vty)))
``,
  REPEAT STRIP_TAC >>

  IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_thm >>
  PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `e`) >>

  (* either both evaluation error, ... *)
  FULL_SIMP_TAC (std_ss) [] >>

  (* get rid of all the wrong types (Mem first) *)
  Cases_on `bir_val_is_Mem v` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_is_Mem_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_dest_bool_val_def] >>
    PAT_X_ASSUM ``BType_Mem A B = C`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def]
  ) >>
  Cases_on `type_of_bir_val v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_checker_TO_type_of]
  ) >>

  (* same for wrong Imm sizes *)
  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def, BType_Bool_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [GSYM bir_val_checker_TO_type_of, bir_val_is_Imm_s_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_dest_bool_val_def]
  )
);

val bir_eval_exp_BOOL_SOME_sound_thm = store_thm(
   "bir_eval_exp_BOOL_SOME_sound_thm", ``
!s sys H e bv.
  (birs_symb_matchstate sys H s) ==>
  (option_CASE (bir_eval_exp e s.bst_environ) NONE bir_dest_bool_val = SOME bv) ==>
  (?sv. (birs_eval_exp e sys.bsst_environ = SOME (sv, BType_Imm Bit1)) /\
        (bir_eval_exp e s.bst_environ = SOME (BVal_Imm (Imm1 (bool2w bv)))) /\
        (birs_interpret_fun H sv = bir_eval_exp e s.bst_environ))
``,
  REPEAT STRIP_TAC >>

  IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_thm >>
  PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `e`) >>

  (* can't be evaluation errors *)
  FULL_SIMP_TAC (std_ss) [] >- (
    FULL_SIMP_TAC (std_ss) []
  ) >>

  (* get rid of all the wrong types (Mem first) *)
  Cases_on `bir_val_is_Mem v` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_is_Mem_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_dest_bool_val_def] >>
    PAT_X_ASSUM ``BType_Mem A B = C`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def]
  ) >>
  Cases_on `type_of_bir_val v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_checker_TO_type_of]
  ) >>

  (* same for wrong Imm sizes *)
  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def, BType_Bool_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [GSYM bir_val_checker_TO_type_of, bir_val_is_Imm_s_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_dest_bool_val_def]
  ) >>

  REWRITE_TAC [bir_immTheory.bool2b_def]
);

val bir_eval_exp_EXISTS_IS_NONE_sound_thm = store_thm(
   "bir_eval_exp_EXISTS_IS_NONE_sound_thm", ``
!s sys H el.
  (birs_symb_matchstate sys H s) ==>
  (EXISTS IS_NONE (MAP (\e. bir_eval_exp e s.bst_environ) el)
   =
   EXISTS IS_NONE (MAP (\e. birs_eval_exp e sys.bsst_environ) el))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.EXISTS_MEM] >>

  Induct_on `el` >> (
    FULL_SIMP_TAC std_ss [listTheory.MEM, listTheory.MAP]
  ) >>

  METIS_TAC [birs_symb_matchstate_IMP_bir_symb_eval_exp_thm, option_CLAUSES]
);

fun birs_exec_stmt_assert_assume_sound_TAC qstatus =
  (*
  val qstatus = `BST_AssertionViolated`;
  *)
  Cases_on `option_CASE (bir_eval_exp ex s.bst_environ) NONE bir_dest_bool_val` >- (
    IMP_RES_TAC bir_eval_exp_BOOL_NONE_sound_thm >> (
      (* finish the error cases as usual/above *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>
      IMP_RES_TAC (Q.SPECL [`s`, `sys`] birs_state_set_typeerror_SING_symb_matchstate_thm) >>
      TRY HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (std_ss) []
    )
  ) >>

  IMP_RES_TAC bir_eval_exp_BOOL_SOME_sound_thm >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>

  IMP_RES_TAC (SIMP_RULE std_ss [IN_SING] (Q.SPEC qstatus birs_symb_matchstate_UPD_status_thm)) >>
  IMP_RES_TAC birs_symb_matchstate_COND_thm >>
  METIS_TAC [birs_state_t_fupdcanon]
;

val birs_exec_stmt_assert_sound_thm = store_thm(
   "birs_exec_stmt_assert_sound_thm", ``
!ex s s' sys Pi H.
  (bir_exec_stmt_assert ex s = s') ==>
  (birs_exec_stmt_assert ex sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_assert_def, birs_exec_stmt_assert_def] >>

  birs_exec_stmt_assert_assume_sound_TAC `BST_AssertionViolated`
);

val birs_exec_stmt_assume_sound_thm = store_thm(
   "birs_exec_stmt_assume_sound_thm", ``
!ex s s' sys Pi H.
  (bir_exec_stmt_assume ex s = s') ==>
  (birs_exec_stmt_assume ex sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_assume_def, birs_exec_stmt_assume_def] >>

  birs_exec_stmt_assert_assume_sound_TAC `BST_AssumptionViolated`
);

val birs_exec_stmt_observe_sound_thm = store_thm(
   "birs_exec_stmt_observe_sound_thm", ``
!oid ec el obf s s' sys Pi H.
  (SND (bir_exec_stmt_observe oid ec el obf s) = s') ==>
  (birs_exec_stmt_observe oid ec el obf sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_observe_def, birs_exec_stmt_observe_def] >>

  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [LET_DEF] >>

  (* obs condition does not give a bool *)
  Cases_on `option_CASE (bir_eval_exp ec s.bst_environ) NONE bir_dest_bool_val` >> (
    FULL_SIMP_TAC (std_ss) []
  ) >- (
    IMP_RES_TAC bir_eval_exp_BOOL_NONE_sound_thm >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def]
    ) >> (
      Cases_on `EXISTS IS_NONE (MAP (\e. birs_eval_exp e sys.bsst_environ) el)` >> (
        FULL_SIMP_TAC (std_ss) [listTheory.EXISTS_DEF]
      )
    ) >> (
      (* finish the error cases as usual/above *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>
      IMP_RES_TAC (Q.SPECL [`s`, `sys`] birs_state_set_typeerror_SING_symb_matchstate_thm) >>
      TRY HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (std_ss) []
    )
  ) >>

  (* the condition evaluates correctly, but type error in the obs expression *)
  IMP_RES_TAC bir_eval_exp_BOOL_SOME_sound_thm >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>
  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>

    Cases_on `EXISTS IS_NONE (MAP (\e. bir_eval_exp e s.bst_environ) el)` >> (
      Cases_on `EXISTS IS_NONE (MAP (\e. birs_eval_exp e sys.bsst_environ) el)` >> (
        FULL_SIMP_TAC (std_ss) [listTheory.EXISTS_DEF, bir_eval_exp_EXISTS_IS_NONE_sound_thm]
      )
    ) >> (
      TRY (
        (* finish the error cases as usual/above *)
        FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def] >>
        IMP_RES_TAC (Q.SPECL [`s`, `sys`] birs_state_set_typeerror_SING_symb_matchstate_thm) >>
        TRY HINT_EXISTS_TAC >>
        FULL_SIMP_TAC (std_ss) [] >>
        FAIL_TAC "not there yet"
      )
    ) >> (
      TRY (
        PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
        PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
        FULL_SIMP_TAC (std_ss) [IN_SING] >>
        FAIL_TAC "not there yet"
      )
    ) >>

    METIS_TAC [bir_eval_exp_EXISTS_IS_NONE_sound_thm]
  )
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
  REPEAT STRIP_TAC >>

  (* TODO: there is a branch where this is justified *)
  FULL_SIMP_TAC (std_ss)
    [prove(``!ex st. bir_exec_stmt_halt ex st =
       st with bst_status := BST_Halted (BVal_Imm (Imm1 0w))``, cheat),
     birs_exec_stmt_halt_def] >>

  PAT_X_ASSUM ``A = (Pi:birs_state_t -> bool)`` (ASSUME_TAC o GSYM) >>
  PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++PRED_SET_ss) [birs_symb_matchstate_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_TYPES_ss++birs_state_ss) [birs_symb_symbols_def]
);

val birs_eval_label_exp_SOME_sound_thm = store_thm(
   "birs_eval_label_exp_SOME_sound_thm", ``
!sys s H le ls l.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_label_exp le sys.bsst_environ sys.bsst_pcond = SOME ls) ==>
  (?l. l IN ls /\ bir_eval_label_exp le s.bst_environ = SOME l)
``,
  REPEAT STRIP_TAC >>

  Cases_on `le` >> (
    FULL_SIMP_TAC std_ss [birs_eval_label_exp_def, bir_eval_label_exp_def]
  ) >- (
    METIS_TAC [IN_SING]
  ) >>

  Cases_on `birs_eval_exp b sys.bsst_environ` >- (
    IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_NONE_thm >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES]
  ) >>

  Cases_on `x` >>
  IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_SOME_thm >>

  Cases_on `v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pair_CASE_def]
  ) >> Cases_on `r` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pair_CASE_def]
  ) >>

  PAT_X_ASSUM ``{B C | D C} = A`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++PRED_SET_ss) [option_CLAUSES] >>

  METIS_TAC [birs_symb_matchstate_def]
);

val birs_eval_label_exp_NONE_sound_thm = store_thm(
   "birs_eval_label_exp_NONE_sound_thm", ``
!sys s H le.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_label_exp le sys.bsst_environ sys.bsst_pcond = NONE) ==>
  (bir_eval_label_exp le s.bst_environ = NONE)
``,
  REPEAT STRIP_TAC >>

  Cases_on `le` >> (
    FULL_SIMP_TAC std_ss [birs_eval_label_exp_def, bir_eval_label_exp_def]
  ) >>

  Cases_on `birs_eval_exp b sys.bsst_environ` >- (
    IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_NONE_thm >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES]
  ) >>

  Cases_on `x` >>
  IMP_RES_TAC birs_symb_matchstate_IMP_bir_symb_eval_exp_SOME_thm >>

  Cases_on `v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pair_CASE_def]
  ) >>

  Cases_on `r` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pair_CASE_def]
  )
);


val birs_exec_stmt_jmp_to_label_sound_thm = store_thm(
   "birs_exec_stmt_jmp_to_label_sound_thm", ``
!sys s H p l sys' s'.
  (birs_symb_matchstate sys H s) ==>
  (birs_exec_stmt_jmp_to_label p sys l = sys') ==>
  (bir_exec_stmt_jmp_to_label p l s = s') ==>
  (birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [birs_exec_stmt_jmp_to_label_def, bir_exec_stmt_jmp_to_label_def] >>

  Cases_on `MEM l (bir_labels_of_program p)` >> (
    FULL_SIMP_TAC std_ss [] >>
    PAT_X_ASSUM ``A = (sys':birs_state_t)`` (ASSUME_TAC o GSYM) >>
    PAT_X_ASSUM ``A = (s':bir_state_t)`` (ASSUME_TAC o GSYM) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) [birs_symb_matchstate_def, birs_symb_symbols_def]
  )
);

val birs_exec_stmt_jmp_sound_thm = store_thm(
   "birs_exec_stmt_jmp_sound_thm", ``
!p le s s' sys Pi H.
  (bir_exec_stmt_jmp p le s = s') ==>
  (birs_exec_stmt_jmp p le sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_jmp_def, birs_exec_stmt_jmp_def] >>

  Cases_on `birs_eval_label_exp le sys.bsst_environ sys.bsst_pcond` >- (
    (* type error: NONE case *)
    IMP_RES_TAC birs_eval_label_exp_NONE_sound_thm >>

    (* finish the error cases as usual/above *)
    FULL_SIMP_TAC (std_ss) [] >>
    IMP_RES_TAC (Q.SPECL [`s`, `sys`] birs_state_set_typeerror_SING_symb_matchstate_thm) >>
    TRY HINT_EXISTS_TAC >>
    FULL_SIMP_TAC (std_ss) []
  ) >>

  (* when we compute a label set: SOME case *)
  IMP_RES_TAC birs_eval_label_exp_SOME_sound_thm >>
  FULL_SIMP_TAC (std_ss) [] >>

  METIS_TAC [birs_exec_stmt_jmp_to_label_sound_thm, IN_IMAGE]
);

val birs_symb_matchstate_BRANCH_thm = store_thm(
   "birs_symb_matchstate_BRANCH_thm", ``
!sys H s e sv bv.
  (birs_symb_matchstate sys H s) ==>
  (birs_eval_exp e sys.bsst_environ = SOME (sv,BType_Imm Bit1)) ==>
  (bir_eval_exp e s.bst_environ = SOME (BVal_Imm (Imm1 (bool2w bv)))) ==>
  (birs_interpret_fun H sv = bir_eval_exp e s.bst_environ) ==>
  (birs_symb_matchstate (birs_branch bv sv sys) H s)
``,
  REPEAT STRIP_TAC >>
  Cases_on `bv` >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def, birs_branch_def] >>

    CONJ_TAC >- (
      METIS_TAC [symb_interpr_for_symbs_COND_thm]
    )
  ) >> (
    REV_FULL_SIMP_TAC (std_ss) [GSYM bir_val_true_def] >>

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def, bir_immTheory.bool2w_def] >>
    wordsLib.WORD_DECIDE_TAC
  )
);

val birs_exec_stmt_cjmp_sound_thm = store_thm(
   "birs_exec_stmt_cjmp_sound_thm", ``
!p ex le1 le2 s s' sys Pi H.
  (bir_exec_stmt_cjmp p ex le1 le2 s = s') ==>
  (birs_exec_stmt_cjmp p ex le1 le2 sys = Pi) ==>
  (birs_symb_matchstate sys H s) ==>
  (?sys'. sys' IN Pi /\ birs_symb_matchstate sys' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss)
    [bir_exec_stmt_cjmp_def, birs_exec_stmt_cjmp_def] >>

  Cases_on `option_CASE (bir_eval_exp ex s.bst_environ) NONE bir_dest_bool_val` >- (
    IMP_RES_TAC bir_eval_exp_BOOL_NONE_sound_thm >> (
      (* finish the error cases as usual/above *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def, LET_DEF] >>
      IMP_RES_TAC (Q.SPECL [`s`, `sys`] birs_state_set_typeerror_SING_symb_matchstate_thm) >>
      TRY HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (std_ss) []
    )
  ) >>

  IMP_RES_TAC bir_eval_exp_BOOL_SOME_sound_thm >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [pair_CASE_def, LET_DEF] >>

  FULL_SIMP_TAC std_ss [GSYM birs_branch_def, GSYM birs_symb_matchonestate_def] >>
  IMP_RES_TAC birs_symb_matchstate_BRANCH_thm >>

  `if x then
          birs_symb_matchonestate (birs_exec_stmt_jmp p le1 (birs_branch T sv sys)) H
            (bir_exec_stmt_jmp p le1 s)
        else
          birs_symb_matchonestate (birs_exec_stmt_jmp p le2 (birs_branch F sv sys)) H
            (bir_exec_stmt_jmp p le2 s)` by (
    
    Cases_on `x` >> (
      METIS_TAC[REWRITE_RULE [GSYM birs_symb_matchonestate_def] (SIMP_RULE std_ss [] birs_exec_stmt_jmp_sound_thm)]
    )
  ) >>

  IMP_RES_TAC birs_symb_matchstate_COND_UNION_thm
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
