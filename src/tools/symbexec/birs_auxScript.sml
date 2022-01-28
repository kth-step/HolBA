open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open symb_recordTheory;

open bir_symb_sound_coreTheory;

val _ = new_theory "birs_aux";

val birs_symb_symbst_pc_thm = store_thm(
   "birs_symb_symbst_pc_thm", ``
!s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
);

val birs_symb_concst_pc_thm = store_thm(
   "birs_symb_concst_pc_thm", ``
!s.
  symb_concst_pc (birs_symb_to_concst s) = s.bst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_concst_pc_def, bir_symbTheory.birs_symb_to_concst_def]
);

val symb_symbols_set_ALT_thm = store_thm(
   "symb_symbols_set_ALT_thm", ``
!sr Pi.
  symb_symbols_set sr Pi = (BIGUNION (IMAGE (symb_symbols sr) Pi))
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_def, IMAGE_DEF]
);

val birs_symb_symbols_set_EQ_thm = store_thm(
   "birs_symb_symbols_set_EQ_thm", ``
!prog Pi.
  symb_symbols_set (bir_symb_rec_sbir prog) (IMAGE birs_symb_to_symbst Pi) = BIGUNION (IMAGE birs_symb_symbols Pi)
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_ALT_thm, EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [IN_BIGUNION_IMAGE] >>
  FULL_SIMP_TAC (std_ss) [IN_IMAGE] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm]
  )
);

val birs_exps_of_senv_def = Define `
    birs_exps_of_senv senv =
      {e | (?vn. senv vn = SOME e)}
`;

val birs_exps_of_senv_COMP_def = Define `
    birs_exps_of_senv_COMP excset senv =
      {e | (?vn. (~(vn IN excset)) /\ senv vn = SOME e)}
`;

val birs_exps_of_senv_thm = store_thm(
   "birs_exps_of_senv_thm", ``
!senv.
  birs_exps_of_senv senv
  =
  birs_exps_of_senv_COMP EMPTY senv
``,
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def, birs_exps_of_senv_def]
);

val birs_exps_of_senv_COMP_thm = store_thm(
   "birs_exps_of_senv_COMP_thm", ``
!sr Pi.
  (!excset. birs_exps_of_senv_COMP excset (K NONE) = EMPTY) /\
  (!excset senv vn sv. birs_exps_of_senv_COMP excset ((vn =+ (SOME sv)) senv) =
    if vn IN excset then
      birs_exps_of_senv_COMP (vn INSERT excset) senv
    else
      sv INSERT (birs_exps_of_senv_COMP (vn INSERT excset) senv)) /\
  (!excset senv vn. birs_exps_of_senv_COMP excset ((vn =+ NONE) senv) = (birs_exps_of_senv_COMP (vn INSERT excset) senv))
``,
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def]
  ) >>

  Cases_on `vn IN excset` >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [EXTENSION] >>
    REPEAT STRIP_TAC >> EQ_TAC >> (
      REPEAT STRIP_TAC >>
      METIS_TAC [combinTheory.APPLY_UPDATE_THM, optionTheory.option_CLAUSES]
    )
  )
);

val birs_symb_symbols_thm = store_thm(
   "birs_symb_symbols_thm", ``
!sys.
  birs_symb_symbols sys = (BIGUNION (IMAGE bir_vars_of_exp (birs_exps_of_senv sys.bsst_environ))) UNION (bir_vars_of_exp sys.bsst_pcond)
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def, IMAGE_DEF, birs_exps_of_senv_def, IN_GSPEC_IFF]
);

val birs_symb_symbst_pc_thm = store_thm(
   "birs_symb_symbst_pc_thm", ``
!s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
);



val _ = export_theory();
