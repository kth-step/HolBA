open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open symb_interpretTheory;
open symb_recordTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open symb_typesLib;
open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "birs_rules";



val birs_pcondinf_def = Define `
    birs_pcondinf pcond =
  (!H.
    (birs_interpr_welltyped H) ==>
    (symb_interpr_for_symbs (bir_vars_of_exp pcond) H) ==>
    (birs_interpret_fun H pcond = SOME bir_val_false)
  )
`;

val birs_pcondinf_thm = store_thm(
   "birs_pcondinf_thm", ``
!bprog pcond.
  birs_pcondinf pcond ==>
  symb_pcondinf (bir_symb_rec_sbir bprog) pcond
``,
  REWRITE_TAC [symb_rulesTheory.symb_pcondinf_def, birs_pcondinf_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def, symb_interpr_symbpcond_def, bir_bool_expTheory.bir_val_TF_dist]
);

val birs_pcondwiden_def = Define `
    birs_pcondwiden pcond pcond' =
    (!H.
      (birs_interpr_welltyped H) ==>
      (symb_interpr_for_symbs ((bir_vars_of_exp pcond) UNION (bir_vars_of_exp pcond')) H) ==>
      (birs_interpret_fun H pcond = SOME bir_val_true) ==>
      (birs_interpret_fun H pcond' = SOME bir_val_true))
`;

val birs_pcondwiden_thm = store_thm(
   "birs_pcondwiden_thm", ``
!bprog pcond pcond'.
  symb_pcondwiden (bir_symb_rec_sbir bprog) pcond pcond' <=>
  birs_pcondwiden pcond pcond'
``,
  REWRITE_TAC [symb_rulesTheory.symb_pcondwiden_def, birs_pcondwiden_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def, symb_interpr_symbpcond_def, bir_bool_expTheory.bir_val_TF_dist]
);


(* ******************************************************* *)
(*      ASSERT statement justification                     *)
(* ******************************************************* *)
(* this is an adjusted copy of "bir_disj1_false" from "bir_exp_equivTheory" *)
local
  open bir_bool_expTheory
in
val bir_conj_true = store_thm(
   "bir_conj_true",
  ``!A B.
      (bir_eval_bin_exp BIExp_And (A) (B) = SOME bir_val_true) ==>
      (A = SOME bir_val_true /\
       B = SOME bir_val_true)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def,
                                      bir_val_false_def] >> (
  Cases_on `A` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `B` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `b` >> Cases_on `b'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_exp_def]
  ) >>
  blastLib.FULL_BBLAST_TAC
)
);
end;

val birs_pcondwiden_AND_thm = store_thm(
   "birs_pcondwiden_AND_thm", ``
!pre cond.
  birs_pcondwiden (BExp_BinExp BIExp_And pre cond) pre
``,
  REWRITE_TAC [birs_pcondwiden_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  METIS_TAC [bir_conj_true]
);


val assert_spec_thm = store_thm(
   "assert_spec_thm", ``
!bprog sys L lbl1 env1 status pre cond lbl2 env2.
  (symb_hl_step_in_L_sound (bir_symb_rec_sbir bprog)
    (sys, L, IMAGE birs_symb_to_symbst {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>;
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := BST_AssertionViolated;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>})) ==>
  (lbl1 <> lbl2 \/
   status <> BST_AssertionViolated) ==>
  (birs_pcondinf (BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond))) ==>
  (symb_hl_step_in_L_sound (bir_symb_rec_sbir bprog)
    (sys, L, IMAGE birs_symb_to_symbst {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := pre|>}))
``,
  REPEAT STRIP_TAC >> (
    IMP_RES_TAC symb_rulesTheory.symb_rule_INF_thm >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ``birs_symb_to_symbst <|bsst_pc := lbl2; bsst_environ := env2;
                  bsst_status := BST_AssertionViolated;
                  bsst_pcond :=
                    BExp_BinExp BIExp_And pre (BExp_UnaryExp BIExp_Not cond')|>``) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [IMAGE_INSERT, IMAGE_EMPTY, birs_symb_to_symbst_def] >>

    `symb_pcondinf (bir_symb_rec_sbir bprog)
          (BExp_BinExp BIExp_And pre (BExp_UnaryExp BIExp_Not cond'))` by (
      METIS_TAC [birs_pcondinf_thm, symb_symbst_pcond_def]
    ) >>

    FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [symb_symbst_pcond_def, DIFF_INSERT, DIFF_EMPTY, DELETE_INSERT, EMPTY_DELETE] >>
    REV_FULL_SIMP_TAC (std_ss) [] >>

    Q.ABBREV_TAC `sys2 = SymbSymbSt lbl1 env1 (BExp_BinExp BIExp_And pre cond') status` >>
    Q.ABBREV_TAC `sys2' = SymbSymbSt lbl1 env1 pre status` >>

    ASSUME_TAC (
      (Q.SPECL [`sys`, `L`, `{sys2}`, `sys2`, `sys2'`] o
       SIMP_RULE std_ss [bir_symb_soundTheory.birs_symb_ARB_val_sound_thm] o
       MATCH_MP symb_rulesTheory.symb_rule_CONS_E_thm o
       Q.SPEC `bprog`)
         bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>

    `symb_pcondwiden_sys (bir_symb_rec_sbir bprog) sys2 sys2'` by (
      Q.UNABBREV_TAC `sys2` >>
      Q.UNABBREV_TAC `sys2'` >>

      SIMP_TAC (std_ss++symb_TYPES_ss) [symb_rulesTheory.symb_pcondwiden_sys_def, symb_symbst_extra_def, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_pcond_def] >>
      REWRITE_TAC [birs_pcondwiden_thm, birs_pcondwiden_AND_thm]
    ) >>

    FULL_SIMP_TAC (std_ss) [] >>
    REV_FULL_SIMP_TAC (std_ss) [DIFF_INSERT, SING_DELETE, DIFF_EMPTY, UNION_EMPTY]
  )
);


(* ******************************************************* *)
(*      SUBST rule                                         *)
(* ******************************************************* *)
val symb_rule_SUBST_SING_thm = prove(``
!sr.
!sys L sys2 var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, {sys2})) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>

  (symb_simplification sr (symb_symbst_pcond sys2) symbexp symbexp') ==>

  (symb_hl_step_in_L_sound sr (sys, L, {symb_symbst_store_update var symbexp' sys2}))
``,
  REPEAT STRIP_TAC >>

  `({sys2} DIFF {sys2}) UNION {symb_symbst_store_update var symbexp' sys2} = {symb_symbst_store_update var symbexp' sys2}` by (
    METIS_TAC [pred_setTheory.DIFF_EQ_EMPTY, pred_setTheory.UNION_EMPTY]
  ) >>

  METIS_TAC [symb_rulesTheory.symb_rule_SUBST_thm]
);

val birs_rule_SUBST_spec_thm = store_thm(
   "birs_rule_SUBST_spec_thm", ``
         !prog sys L sys2 sys2' lbl envl status pcond vn symbexp symbexp'.
           (sys2 =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           (sys2' =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir prog) (sys,L,IMAGE birs_symb_to_symbst {sys2}) ==>
           birs_simplification pcond symbexp symbexp' ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir prog) (sys,L,IMAGE birs_symb_to_symbst {sys2'})
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC (
    (Q.SPECL [`sys`, `L`, `birs_symb_to_symbst sys2`, `vn`, `symbexp`, `symbexp'`] o
     SIMP_RULE std_ss [bir_symb_soundTheory.birs_symb_ARB_val_sound_thm] o
     MATCH_MP symb_rule_SUBST_SING_thm o
     Q.SPEC `prog`)
       bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>

  REV_FULL_SIMP_TAC (std_ss++birs_state_ss)
    [IMAGE_SING, birs_symb_to_symbst_def, symb_symbst_store_def, symb_symbst_pcond_def,
     bir_symb_simpTheory.birs_simplification_thm,
     symb_symbst_store_update_def, birs_auxTheory.birs_gen_env_thm,
     combinTheory.UPDATE_APPLY]
);




(* ******************************************************* *)
(*      STEP rule                                          *)
(* ******************************************************* *)
val birs_rule_STEP_gen1_thm = store_thm(
   "birs_rule_STEP_gen1_thm", ``
!prog sys.
  (bir_prog_has_no_halt prog) ==>

  (symb_hl_step_in_L_sound (bir_symb_rec_sbir prog)
    (sys,
     {symb_symbst_pc sys},
     IMAGE birs_symb_to_symbst
       (birs_exec_step prog (birs_symb_from_symbst sys))))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_symb_soundTheory.birs_symb_step_sound_thm >>

  IMP_RES_TAC symb_rulesTheory.symb_rule_STEP_thm >>
  POP_ASSUM (ASSUME_TAC o SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss) [] o REWRITE_RULE [Once bir_symbTheory.bir_symb_rec_sbir_def]) >>

  METIS_TAC [IN_SING]
);

val birs_rule_STEP_gen2_thm = store_thm(
   "birs_rule_STEP_gen2_thm", ``
!prog bsys.
  (bir_prog_has_no_halt prog) ==>

  (symb_hl_step_in_L_sound (bir_symb_rec_sbir prog)
    (birs_symb_to_symbst bsys,
     {bsys.bsst_pc},
     IMAGE birs_symb_to_symbst
       (birs_exec_step prog bsys)))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_rule_STEP_gen1_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `birs_symb_to_symbst bsys`) >>

  FULL_SIMP_TAC std_ss [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_auxTheory.birs_symb_symbst_pc_thm]
);


(* ******************************************************* *)
(*      NO FRESH SYMBS                                     *)
(* ******************************************************* *)
val birs_fresh_symbs_def = Define `
    birs_fresh_symbs bs1 bs2 =
      ((birs_symb_symbols bs2) DIFF (birs_symb_symbols bs1))
`;

val birs_NO_fresh_symbs_def = Define `
    birs_NO_fresh_symbs bs1 bs2 =
      (birs_fresh_symbs bs1 bs2 = EMPTY)
`;

val birs_set_fresh_symbs_def = Define `
    birs_set_fresh_symbs bs sbs =
      ((BIGUNION (IMAGE birs_symb_symbols sbs)) DIFF (birs_symb_symbols bs))
`;

val birs_set_NO_fresh_symbs_def = Define `
    birs_set_NO_fresh_symbs bs sbs =
      (birs_set_fresh_symbs bs sbs = EMPTY)
`;

val birs_NO_fresh_symbs_SUFFICIENT_thm = store_thm(
   "birs_NO_fresh_symbs_SUFFICIENT_thm", ``
!bs1 bs2.
  (bs1.bsst_environ = bs2.bsst_environ /\
   bs1.bsst_pcond   = bs2.bsst_pcond) ==>
  (birs_NO_fresh_symbs bs1 bs2)
``,
  SIMP_TAC std_ss [birs_NO_fresh_symbs_def, birs_fresh_symbs_def, birs_symb_symbols_def, DIFF_EQ_EMPTY]
);

val birs_NO_fresh_symbs_SUFFICIENT2_thm = store_thm(
   "birs_NO_fresh_symbs_SUFFICIENT2_thm", ``
!bs1 bs2 bs2'.
  (birs_NO_fresh_symbs bs1 bs2 /\
   bs2.bsst_environ = bs2'.bsst_environ /\
   bs2.bsst_pcond   = bs2'.bsst_pcond) ==>
  (birs_NO_fresh_symbs bs1 bs2')
``,
  SIMP_TAC std_ss [birs_NO_fresh_symbs_def, birs_fresh_symbs_def, birs_symb_symbols_def, DIFF_EQ_EMPTY] >>
  REPEAT STRIP_TAC >>
  METIS_TAC []
);

(* TODO: this should go to auxTheory *)
val SUBSET_of_DIFF_2_thm = store_thm(
   "SUBSET_of_DIFF_2_thm",
  ``!s t v.
    s SUBSET t ==>
    ((v DIFF t) SUBSET (v DIFF s))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF] >>
  METIS_TAC []
);

val birs_NO_fresh_symbs_SUFFICIENT3_thm = store_thm(
   "birs_NO_fresh_symbs_SUFFICIENT3_thm", ``
!bs1 bs1' bs2.
  (birs_NO_fresh_symbs bs1 bs2 /\
   (birs_symb_symbols bs1) SUBSET (birs_symb_symbols bs1')) ==>
  (birs_NO_fresh_symbs bs1' bs2)
``,
  SIMP_TAC std_ss [birs_NO_fresh_symbs_def, birs_fresh_symbs_def, DIFF_EQ_EMPTY] >>
  REPEAT STRIP_TAC >>

  METIS_TAC [SUBSET_of_DIFF_2_thm, SUBSET_EMPTY]
);

val BIGUNION_IMAGE_DIFF_EQ_thm = store_thm(
   "BIGUNION_IMAGE_DIFF_EQ_thm", ``
!f s1 s2s.
  ((BIGUNION (IMAGE f s2s)) DIFF s1 = BIGUNION (IMAGE (\s2. (f s2) DIFF s1) s2s))
``,
  SIMP_TAC (std_ss) [EXTENSION, IN_BIGUNION_IMAGE, IN_DIFF] >>
  METIS_TAC []
);

val birs_set_fresh_symbs_thm = store_thm(
   "birs_set_fresh_symbs_thm", ``
!bs sbs.
  (birs_set_fresh_symbs bs sbs = BIGUNION (IMAGE (\bs2. birs_fresh_symbs bs bs2) sbs))
``,
  SIMP_TAC std_ss [birs_set_fresh_symbs_def, birs_fresh_symbs_def, BIGUNION_IMAGE_DIFF_EQ_thm]
);

val birs_set_NO_fresh_symbs_thm = store_thm(
   "birs_set_NO_fresh_symbs_thm", ``
!bs sbs.
  (birs_set_NO_fresh_symbs bs sbs =
   !bs2. bs2 IN sbs ==> (birs_NO_fresh_symbs bs bs2))
``,
  SIMP_TAC std_ss [birs_set_NO_fresh_symbs_def, birs_set_fresh_symbs_thm, birs_NO_fresh_symbs_def] >>
  SIMP_TAC (std_ss) [EXTENSION, IN_BIGUNION_IMAGE, NOT_IN_EMPTY] >>
  METIS_TAC []
);

val birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm = store_thm(
   "birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm", ``
!bsys be sv ty pcond'.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty) /\
   bir_vars_of_exp pcond' = bir_vars_of_exp bsys.bsst_pcond UNION bir_vars_of_exp sv) ==>
  (birs_symb_symbols bsys =
   birs_symb_symbols (bsys with bsst_pcond := pcond'))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm >>

  ASM_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def] >>
  IMP_RES_TAC SUBSET_UNION_ABSORPTION >>

  METIS_TAC [UNION_COMM, UNION_ASSOC]
);

val birs_eval_exp_IMP_symb_symbols_EQ_pcond_status_thm = store_thm(
   "birs_eval_exp_IMP_symb_symbols_EQ_pcond_status_thm", ``
!bsys be sv ty pcond' status'.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty) /\
   bir_vars_of_exp pcond' = bir_vars_of_exp bsys.bsst_pcond UNION bir_vars_of_exp sv) ==>
  (birs_symb_symbols bsys =
   birs_symb_symbols (bsys with <|bsst_status := status'; bsst_pcond := pcond'|>))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>

  ASM_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def]
);

(* TODO: this definition needs to go somewhere else and must be integrated with the other places where it belongs (into previous definitions and proofs) *)
val birs_vars_of_env_def = Define `
    birs_vars_of_env senv =
      BIGUNION {bir_vars_of_exp e | (?vn. senv vn = SOME e)}
`;

(*
TODO: these two theorems are the same, did I prove them twice? (bir_symbTheory should be "before")
bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm
bir_symb_soundTheory.birs_eval_exp_IMP_varset_thm
*)
val birs_eval_exp_IMP_symbs_SUBSET_senv_thm = store_thm(
   "birs_eval_exp_IMP_symbs_SUBSET_senv_thm", ``
!e senv sv ty.
       birs_eval_exp e senv = SOME (sv,ty) ==>
       bir_vars_of_exp sv SUBSET birs_vars_of_env senv
``,
  METIS_TAC [bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm, birs_vars_of_env_def]
);

val birs_eval_exp_IMP_vars_of_env_SUBSET_thm = store_thm(
   "birs_eval_exp_IMP_vars_of_env_SUBSET_thm", ``
!env be sv ty vn.
  (birs_eval_exp be env = SOME (sv,ty)) ==>
  (birs_vars_of_env (birs_update_env (vn,sv) env) SUBSET (birs_vars_of_env env))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_symbs_SUBSET_senv_thm >>

  FULL_SIMP_TAC (std_ss) [SUBSET_DEF] >>

  FULL_SIMP_TAC (std_ss) [birs_vars_of_env_def] >>
  FULL_SIMP_TAC (std_ss) [FORALL_IN_BIGUNION] >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Cases_on `vn = vn'` >> (
    FULL_SIMP_TAC (std_ss) [birs_update_env_def, combinTheory.UPDATE_APPLY] >>
    METIS_TAC []
  )
);

val birs_eval_exp_IMP_symb_symbols_SUBSET_environ_thm = store_thm(
   "birs_eval_exp_IMP_symb_symbols_SUBSET_environ_thm", ``
!bsys be sv ty vn.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty)) ==>
  (birs_symb_symbols (bsys with bsst_environ := birs_update_env (vn,sv) bsys.bsst_environ) SUBSET
   birs_symb_symbols bsys)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_vars_of_env_SUBSET_thm >>

  SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def] >>

  FULL_SIMP_TAC (std_ss) [birs_vars_of_env_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  METIS_TAC [SUBSET_DEF, IN_UNION]
);


val birs_exec_stmt_jmp_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmt_jmp_NO_FRESH_SYMBS", ``
!prog bsys l.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmt_jmp prog l bsys)
``,
    SIMP_TAC std_ss [birs_exec_stmt_jmp_def] >>
    REPEAT STRIP_TAC >>

    CASE_TAC >> (
      SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, FORALL_IN_IMAGE] >>
      REPEAT STRIP_TAC >>

      MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_exec_stmt_jmp_to_label_def] >>
      TRY CASE_TAC >> (
        SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
      )
    )
);

val birs_exec_stmt_cjmp_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmt_cjmp_NO_FRESH_SYMBS", ``
!prog bsys e l1 l2.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmt_cjmp prog e l1 l2 bsys)
``,
  SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_cjmp_def] >>
  REPEAT STRIP_TAC >>
  CASE_TAC >- (
    SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `x` >>
  Cases_on `r` >> (
    SIMP_TAC (std_ss++holBACore_ss) [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
    TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `b` >> (
    SIMP_TAC (std_ss++holBACore_ss) [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
    TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  SIMP_TAC std_ss [IN_UNION] >>

  `birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond q) /\
   birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond (BExp_UnaryExp BIExp_Not q))` by (
    REPEAT STRIP_TAC >> (
      MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>
      ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
      METIS_TAC []
    )
  ) >>

  REPEAT STRIP_TAC >> (
    IMP_RES_TAC (REWRITE_RULE [birs_set_NO_fresh_symbs_thm] birs_exec_stmt_jmp_NO_FRESH_SYMBS) >>
    METIS_TAC [birs_NO_fresh_symbs_SUFFICIENT3_thm, SUBSET_REFL]
  )
);
  

val birs_exec_stmtE_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmtE_NO_FRESH_SYMBS", ``
!prog bsys estmt.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmtE prog estmt bsys)
``,
  REPEAT STRIP_TAC >>
  Cases_on `estmt` >- (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_jmp_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_cjmp_NO_FRESH_SYMBS]
  ) >> (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_halt_def] >>
    SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, FORALL_IN_IMAGE] >>
    MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  )
);

val birs_exec_stmt_assign_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmt_assign_NO_FRESH_SYMBS", ``
!bsys var be.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmt_assign var be bsys)
``,
  SIMP_TAC std_ss [birs_exec_stmt_assign_def] >>
  REPEAT STRIP_TAC >>

  CASE_TAC >- (
    SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `x` >>
  SIMP_TAC (std_ss++holBACore_ss) [pairTheory.pair_CASE_def] >>

  CASE_TAC >- (
    IMP_RES_TAC birs_eval_exp_IMP_symb_symbols_SUBSET_environ_thm >>
    SIMP_TAC (std_ss++holBACore_ss) [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>

    SIMP_TAC std_ss [birs_NO_fresh_symbs_def, birs_fresh_symbs_def] >>
    METIS_TAC [SUBSET_DIFF_EMPTY]
  ) >>

  SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
  TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
  SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
);

val birs_exec_stmt_assert_assume_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmt_assert_assume_NO_FRESH_SYMBS", ``
!bsys be.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmt_assert be bsys) /\
  birs_set_NO_fresh_symbs bsys (birs_exec_stmt_assume be bsys)
``,
  SIMP_TAC std_ss [birs_exec_stmt_assert_def, birs_exec_stmt_assume_def] >>
  REPEAT STRIP_TAC >> (
    CASE_TAC >- (
      SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
      TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    Cases_on `x` >>
    Cases_on `r` >> (
      SIMP_TAC (std_ss++holBACore_ss) [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
      TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    Cases_on `b` >> (
      SIMP_TAC (std_ss++holBACore_ss) [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
      TRY (MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    `birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond q) /\
     !status. birs_symb_symbols bsys = birs_symb_symbols (bsys with <|bsst_status := status;
             bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond (BExp_UnaryExp BIExp_Not q)|>)` by (
      REPEAT STRIP_TAC >- (
        MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>
        ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
        METIS_TAC []
      ) >>

      MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_status_thm >>
      ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
      METIS_TAC []
    ) >>

    REPEAT STRIP_TAC >> (
      ASM_SIMP_TAC std_ss [birs_NO_fresh_symbs_def, birs_fresh_symbs_def] >>
      METIS_TAC [DIFF_EQ_EMPTY]
    )
  )
);

val birs_exec_stmtB_NO_FRESH_SYMBS = store_thm(
   "birs_exec_stmtB_NO_FRESH_SYMBS", ``
!bsys stmt.
  birs_set_NO_fresh_symbs bsys (birs_exec_stmtB stmt bsys)
``,
  REPEAT STRIP_TAC >>
  Cases_on `stmt` >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assign_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assert_assume_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assert_assume_NO_FRESH_SYMBS]
  ) >> (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_observe_def, LET_DEF] >>
    CASE_TAC >- (
      SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
      MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    CASE_TAC >>
    CASE_TAC >> (
      TRY CASE_TAC >> (
        TRY CASE_TAC >> (
          SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
          MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm >>
          SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
        )
      )
    )
  )
);

val birs_exec_step_NO_FRESH_SYMBS = prove(``
!prog bsys.
(*
  (* this assumption is only needed because of the proof with the soundness of steps *)
  (bir_prog_has_no_halt prog) ==>
*)
  birs_set_NO_fresh_symbs bsys (birs_exec_step prog bsys)
``,
  SIMP_TAC std_ss [birs_exec_step_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `birs_state_is_terminated bsys` >- (
    ASM_SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    METIS_TAC [birs_NO_fresh_symbs_SUFFICIENT_thm]
  ) >>

  ASM_SIMP_TAC std_ss [] >>
  Cases_on `bir_get_current_statement prog bsys.bsst_pc` >- (
    ASM_SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT_thm >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_failed_def]
  ) >>

  ASM_SIMP_TAC std_ss [] >>
  REPEAT (POP_ASSUM (K ALL_TAC)) >>
  Cases_on `x` >> (
    ASM_SIMP_TAC std_ss [birs_exec_stmt_def, LET_DEF, birs_exec_stmtE_NO_FRESH_SYMBS]
  ) >>

  SIMP_TAC std_ss [birs_set_NO_fresh_symbs_thm, FORALL_IN_IMAGE] >>
  REPEAT STRIP_TAC >>
  ASSUME_TAC (Q.SPECL [`bsys`, `b`] birs_exec_stmtB_NO_FRESH_SYMBS) >>
  IMP_RES_TAC birs_set_NO_fresh_symbs_thm >>

  Cases_on `birs_state_is_terminated st'` >> (
    ASM_SIMP_TAC std_ss []
  ) >>

  MATCH_MP_TAC birs_NO_fresh_symbs_SUFFICIENT2_thm >>
  SIMP_TAC (std_ss++birs_state_ss) [] >>
  METIS_TAC []
);


(* ******************************************************* *)
(*      STEP SEQ rule                                      *)
(* ******************************************************* *)
val birs_rule_STEP_SEQ_gen_thm = store_thm(
   "birs_rule_STEP_SEQ_gen_thm", ``
!prog bsys1 L bsys2.
  (bir_prog_has_no_halt prog) ==>

  (symb_hl_step_in_L_sound (bir_symb_rec_sbir prog)
    (birs_symb_to_symbst bsys1,
     L,
     IMAGE birs_symb_to_symbst {bsys2}
  )) ==>

  (symb_hl_step_in_L_sound (bir_symb_rec_sbir prog)
    (birs_symb_to_symbst bsys1,
     (bsys2.bsst_pc) INSERT L,
     IMAGE birs_symb_to_symbst (birs_exec_step prog bsys2)
  ))
``,
  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPECL [`prog`, `bsys2`] birs_rule_STEP_gen2_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>


  ASSUME_TAC (Q.SPEC `prog` bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  IMP_RES_TAC symb_rulesTheory.symb_rule_SEQ_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPECL [`birs_symb_to_symbst bsys2`, `birs_symb_to_symbst bsys1`, `IMAGE birs_symb_to_symbst (birs_exec_step prog bsys2)`]) >>
  ASSUME_TAC (REWRITE_RULE [birs_set_NO_fresh_symbs_def, birs_set_fresh_symbs_def] birs_exec_step_NO_FRESH_SYMBS) >>
  FULL_SIMP_TAC std_ss [INTER_EMPTY,
    birs_auxTheory.birs_symb_symbols_set_EQ_thm, bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm] >>

  `L UNION {bsys2.bsst_pc} = bsys2.bsst_pc INSERT L` by (
    METIS_TAC [INSERT_UNION_EQ, UNION_EMPTY, UNION_COMM]
  ) >>

  `(IMAGE birs_symb_to_symbst {bsys2} DIFF {birs_symb_to_symbst bsys2}) UNION
               IMAGE birs_symb_to_symbst (birs_exec_step prog bsys2)
   = IMAGE birs_symb_to_symbst (birs_exec_step prog bsys2)` by (
    SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, DIFF_EQ_EMPTY, UNION_EMPTY]
  ) >>

  METIS_TAC []
);

(*
bir_symbTheory.birs_state_t_bsst_pc
bir_symbTheory.birs_state_t_accfupds
*)

(*
val bprog_tm = ``
BirProgram [] : 'obs_type bir_program_t
``;
val no_halt_thm = prove(``bir_prog_has_no_halt (^bprog_tm)``, cheat);
*)

val _ = export_theory();
