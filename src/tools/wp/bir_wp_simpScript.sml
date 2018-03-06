open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

load "pairLib";

val _ = new_theory "bir_wp_simp";









(* TODO: memory load store updates *)
















val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_imm_ss = rewrites (type_rws ``:bir_imm_t``);
val bir_immtype_ss = rewrites (type_rws ``:bir_immtype_t``);
val bir_wp_simp_eval_binpred_eq_thm = prove(``
    !e1 e2 s.
      (bir_eval_exp (BExp_BinPred BIExp_Equal e1 e2) s = bir_val_true)
      <=>
      (
       (bir_val_is_Imm (bir_eval_exp e1 s)) /\
       (bir_val_is_Imm (bir_eval_exp e2 s)) /\
       (bir_eval_exp e1 s = bir_eval_exp e2 s)
      )
``,

  REWRITE_TAC [bir_eval_exp_def, bir_val_is_Imm_def] >>

  Cases_on `(bir_eval_exp e1 s)` >> (
    Cases_on `(bir_eval_exp e2 s)` >> (
      SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_pred_def, bir_val_true_def]
    )
  ) >>

  Cases_on `type_of_bir_imm b = type_of_bir_imm b'` >- (
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def, bir_imm_expTheory.bir_bin_pred_Equal_REWR] >>

    Cases_on `b = b'` >> (
      ASM_SIMP_TAC (srw_ss()) []
    )
  ) >>

  ASM_SIMP_TAC (std_ss++bir_val_ss) [] >>
  METIS_TAC []
);



val bir_wp_simp_eval_bin_is_Imm_thm = prove(``
    !et e1 e2 s.
      (bir_val_is_Imm (bir_eval_exp (BExp_BinExp et e1 e2) s))
      <=>
      (
       (?sz. bir_val_is_Imm_s sz (bir_eval_exp e1 s) /\
             bir_val_is_Imm_s sz (bir_eval_exp e2 s))
      )
``,

  REWRITE_TAC [bir_eval_exp_def, bir_val_is_Imm_def] >>

  Cases_on `(bir_eval_exp e1 s)` >> (
    Cases_on `(bir_eval_exp e2 s)` >> (
      SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_bin_exp_def, bir_val_is_Imm_s_ALT_DEF]
    )
  ) >>

  Cases_on `type_of_bir_imm b = type_of_bir_imm b'` >- (
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def]
  ) >>

  ASM_SIMP_TAC (std_ss++bir_val_ss) []
);












val bir_wp_simp_eval_and_thm = store_thm("bir_wp_simp_eval_and_thm", ``
    !prem e1 e2.
      (!s. (prem s) ==> (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s = bir_val_true))
      <=>
      (
       (!s. (prem s) ==> (bir_eval_exp e1 s = bir_val_true))
       /\
       (!s. (prem s) ==> (bir_eval_exp e2 s = bir_val_true))
      )
``,

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >> (
      Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
      REV_FULL_SIMP_TAC std_ss [] >>

      subgoal `bir_val_is_Imm (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s)` >- (
        ASM_SIMP_TAC std_ss [bir_val_true_def, bir_val_checker_REWRS]
      ) >>

      subgoal `?sz. bir_val_is_Imm_s sz (bir_eval_exp e1 s) /\ bir_val_is_Imm_s sz (bir_eval_exp e2 s)` >- (
        METIS_TAC [bir_val_is_Imm_s_IMPL, bir_wp_simp_eval_bin_is_Imm_thm]
      ) >>

      Cases_on `bir_eval_exp e1 s` >> (
        Cases_on `bir_eval_exp e2 s` >> (
          FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_val_checker_REWRS]
        )
      ) >>

      FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_exp_def, bir_eval_bin_exp_REWRS, bir_val_true_def] >>

      subgoal `sz = Bit1` >- (
        METIS_TAC [bir_imm_expTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_imm_expTheory.bir_bin_exp_def, bir_imm_expTheory.bir_bin_exp_GET_OPER_def] >>

      Q.PAT_X_ASSUM `A && B = C` (MP_TAC) >>
      blastLib.BBLAST_TAC
    )
  ) >>

  REPEAT STRIP_TAC >>

  REPEAT (Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm))) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  
  ASM_REWRITE_TAC [bir_eval_exp_def, bir_eval_bin_exp_REWRS] >>
  EVAL_TAC
);


bir_is_bool_exp_def
type_of_bir_exp_def
bir_eval_exp_def
bir_eval_bin_pred_def
val bir_wp_simp_eval_imp_thm = store_thm("bir_wp_simp_eval_imp_thm", ``
    !prem e1 e2.
      (bir_is_bool_exp e1) ==>
      (bir_is_bool_exp e2) ==>
      (
       (
        !s. (prem s) ==>
            (bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e1) e2) s = bir_val_true)
       )
       <=>
       (
        !s. ((\s. (prem s) /\ (bir_eval_exp e1 s = bir_val_true)) s)
            ==>
            (bir_eval_exp e2 s = bir_val_true)
       )
      )
``,

  bir_is_bool_exp
);

val bir_wp_simp_eval_or_thm = store_thm("bir_wp_simp_eval_or_thm", ``
    !prem e1 e2.
      (
       !s. (prem s) ==>
           (bir_eval_exp (BExp_BinExp BIExp_Or e1 e2) s = bir_val_true)
      )
      <=>
      (
       !s. ((\s. (prem s) /\ (bir_eval_exp (BExp_UnaryExp BIExp_Not e1) s = bir_val_true)) s)
           ==>
           (bir_eval_exp e2 s = bir_val_true)
      )
``,

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

      Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
      REV_FULL_SIMP_TAC std_ss [] >>

      subgoal `bir_val_is_Imm (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s)` >- (
        ASM_SIMP_TAC std_ss [bir_val_true_def, bir_val_checker_REWRS]
      ) >>

      subgoal `?sz. bir_val_is_Imm_s sz (bir_eval_exp e1 s) /\ bir_val_is_Imm_s sz (bir_eval_exp e2 s)` >- (
        METIS_TAC [bir_val_is_Imm_s_IMPL, bir_wp_simp_eval_bin_is_Imm_thm]
      ) >>

      Cases_on `bir_eval_exp e1 s` >> (
        Cases_on `bir_eval_exp e2 s` >> (
          FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_val_checker_REWRS]
        )
      ) >>

      FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_exp_def, bir_eval_bin_exp_REWRS, bir_val_true_def] >>

      subgoal `sz = Bit1` >- (
        METIS_TAC [bir_imm_expTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_imm_expTheory.bir_bin_exp_def, bir_imm_expTheory.bir_bin_exp_GET_OPER_def] >>

      Q.PAT_X_ASSUM `A && B = C` (MP_TAC) >>
      blastLib.BBLAST_TAC


  ) >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  REPEAT (Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm))) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  subgoal `type_of_bir_imm (bir_eval_exp (BExp_UnaryExp BIExp_Not e1) s) = Bit1` >- (
    METIS_TAC
  )
  
  ASM_REWRITE_TAC [bir_eval_exp_def, bir_eval_bin_exp_REWRS] >>
  EVAL_TAC
);












val bir_eval_exp_indep_env_update_thm = store_thm("bir_eval_exp_indep_env_update_thm", ``
    !vn vt vo e sm.
      (~(vn IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp e (BEnv sm))
       =
       (bir_eval_exp e (BEnv (FUPDATE sm (vn, (vt, vo)))))
      )
``,

  REPEAT STRIP_TAC >>

  Induct_on `e` >> (
    ASM_SIMP_TAC std_ss [bir_eval_exp_def, bir_vars_of_exp_def, pred_setTheory.IMAGE_UNION] >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
  )
);



val bir_wp_simp_eval_subst1_lemma = store_thm("bir_wp_simp_eval_subst1_lemma", ``
    !v ve vn' vt' vo' e sm.
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst1 v ve e) (BEnv (FUPDATE sm (vn', (vt', vo')))))
      )
``,

  REPEAT STRIP_TAC >>

  subgoal `~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp (bir_exp_subst1 v ve e))))` >- (
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>

    Cases_on `v IN bir_vars_of_exp e` >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.IMAGE_UNION] >>
      METIS_TAC []
    )
  ) >>

  METIS_TAC [bir_eval_exp_indep_env_update_thm]
);



val bir_wp_simp_prem_indep_def = Define `
      bir_wp_simp_prem_indep prem vn =
        !sm vt vo. prem (BEnv (FUPDATE sm (vn, (vt, vo)))) = prem (BEnv sm)
`;

val bir_wp_simp_eval_subst1_thm = store_thm("bir_wp_simp_eval_subst1_thm", ``
    !v ve v' e prem.
      (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
      (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (bir_wp_simp_prem_indep prem (bir_var_name v')) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst1 v ve e) s = bir_val_true))
       <=>
       (!s. ((prem s) /\
             (bir_eval_exp (BExp_Den v') s = bir_eval_exp ve s)
(*           (bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den v') ve) s = bir_val_true)*)
            )
            ==>
            (bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) s = bir_val_true)
       )
      )
``,


  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

    Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

 (*   FULL_SIMP_TAC std_ss [bir_wp_simp_eval_binpred_eq_thm] >>*)
    METIS_TAC [bir_exp_subst1_EVAL_EQ_GEN]
  ) >>

  REPEAT STRIP_TAC >>

  Cases_on `s` >>
  Q.RENAME1_TAC `BEnv sm` >>

  Q.ABBREV_TAC `sm' = FUPDATE sm (bir_var_name v', (bir_var_type v', SOME (bir_eval_exp ve (BEnv sm))))` >>

  subgoal `prem (BEnv sm')` >- (
    METIS_TAC [bir_wp_simp_prem_indep_def]
  ) >>

  subgoal `bir_eval_exp (BExp_Den v') (BEnv sm') = bir_eval_exp ve (BEnv sm')` >- (
    SIMP_TAC std_ss [Abbr `sm'`, bir_eval_exp_def, bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    ASM_SIMP_TAC (srw_ss()) [bir_eval_exp_indep_env_update_thm]
  ) >>

  subgoal  `bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm') = bir_val_true` >- (
    METIS_TAC [bir_exp_subst1_EVAL_EQ_GEN]
  ) >>

  METIS_TAC [bir_wp_simp_eval_subst1_lemma]
);



val bir_wp_simp_eval_subst_lemma = store_thm("bir_wp_simp_eval_subst_lemma", ``
    !substs vn' vt' vo' e sm.
      (FEVERY (\(_, t). ~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp t)))) substs) ==>
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp (bir_exp_subst substs e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst substs e) (BEnv (FUPDATE sm (vn', (vt', vo')))))
      )
``,

(*
  REPEAT STRIP_TAC >>
*)

  cheat
);


(* TODO: should probably be somewhere else *)
val bir_exp_conj_from_list_def = Define `
  bir_exp_conj_from_list = FOLDL (\expa. \exp. BExp_BinExp BIExp_And expa exp) (BExp_Const (Imm1 1w))
`;

val bir_exp_varsubst_def = Define `
  bir_exp_varsubst vm = FUN_FMAP (\(x:bir_var_t). BExp_Den (FAPPLY vm x)) (FDOM vm)
`;

val bir_wp_simp_eval_subst_thm = store_thm("bir_wp_simp_eval_subst_thm", ``
    !vvtl vtm vvm bconj e prem.
      (vtm = FUPDATE_LIST FEMPTY (MAP (\(v, _, t). (v, t)) vvtl)) ==>
      (vvm = FUPDATE_LIST FEMPTY (MAP (\(v, v', _). (v, v')) vvtl)) ==>
      (bconj = bir_exp_conj_from_list (MAP (\(_, v', t). BExp_BinPred BIExp_Equal (BExp_Den v') t) vvtl)) ==>
      (EVERY (\v'. ~(v' IN (bir_vars_of_exp e)) /\ EVERY (\t. ~(v' IN (bir_vars_of_exp t))) (MAP (\(_, _, t). t) vvtl))) (MAP (\(_, v', _). v') vvtl) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst vtm e) s = bir_val_true))
       <=>
       (!s. ((prem s) /\
             (bir_eval_exp bconj s = bir_val_true)
            )
            ==>
            (bir_eval_exp (bir_exp_subst (bir_exp_varsubst vvm) e) s = bir_val_true)
       )
      )
``,

(*
  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

  ) >>
*)
  cheat
);
















(* TODO: should be in bir_exp_substitutionsTheory *)
val bir_exp_subst_update_def = Define `
  bir_exp_subst_update s2 s1 = FUN_FMAP (\x. bir_exp_subst s1 (FAPPLY s2 x)) (FDOM s2)
`;

val bir_exp_subst_update_exec_thm = store_thm("bir_exp_subst_update_exec_thm", ``
      (!s1. bir_exp_subst_update FEMPTY s1 = FEMPTY) /\
      (!s1 s2 v e. bir_exp_subst_update (FUPDATE s2 (v,e)) s1 =
           FUPDATE (bir_exp_subst_update s2 s1) (v, bir_exp_subst s1 e))
``,

(*finite_mapTheory.FDOM_FINITE*)
  cheat
);

val bir_exp_subst__def = Define `
  bir_exp_subst_restrict s1 s2 = DRESTRICT s1 (COMPL (FDOM s2))
`;


val bir_exp_subst_bir_exp_subst_thm = store_thm("bir_exp_subst_bir_exp_subst_thm", ``
    !s1 s2 e.
      bir_exp_subst s1 (bir_exp_subst s2 e)
      =
      bir_exp_subst (bir_exp_subst_update s2 s1) (bir_exp_subst (bir_exp_subst_restrict s1 s2) e)
``,

  cheat
);


val _ = export_theory();

