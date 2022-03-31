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

val birs_exec_step_NO_FRESH_SYMBS = prove(``
!prog bsys.
  ((BIGUNION (IMAGE birs_symb_symbols (birs_exec_step prog bsys)))
     DIFF (birs_symb_symbols bsys)
   = EMPTY)
``,
  cheat
);

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
     L UNION {bsys2.bsst_pc},
     IMAGE birs_symb_to_symbst (birs_exec_step prog bsys2)
  ))
``,
  (* symb_rule_SEQ_thm *)
  cheat
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
