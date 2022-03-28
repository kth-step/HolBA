open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open symb_interpretTheory;
open symb_recordTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "birs_rules";


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
  (IS_BIR_CONTRADICTION (BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond))) ==>
  (symb_hl_step_in_L_sound (bir_symb_rec_sbir bprog)
    (sys, L, IMAGE birs_symb_to_symbst {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := pre|>}))
``,
  cheat
);

val symb_rule_SUBST_SING_thm = prove(``
!sr.
!sys L sys2 var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, {sys2})) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>

  (symb_simplification sr sys2 symbexp symbexp') ==>

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
           birs_simplification_e pcond symbexp symbexp' ==>
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
     bir_symb_simpTheory.symb_simplification_thm, bir_symb_simpTheory.birs_simplification_e_thm,
     symb_symbst_store_update_def, birs_auxTheory.birs_gen_env_thm,
     combinTheory.UPDATE_APPLY]
);


val _ = export_theory();
