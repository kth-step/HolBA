open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;

open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

val _ = new_theory "symb_prop_transfer";

(*
NOTATION: DEFINE PROPERTY TRANSFER ASSUMPTIONS AND GOAL
=======================================================
*)
val symb_concst_store_ty_sat_def = Define `
    symb_concst_store_ty_sat sr sty s =
    (!vn ty v.
       (sty vn = SOME ty) ==>
       ((symb_concst_store s) vn = SOME v) ==>
       (sr.sr_typeof_val v = ty))
`;
val symb_symbst_store_ty_def = Define `
    symb_symbst_store_ty sr sys =
    (\vn. OPTION_BIND ((symb_symbst_store sys) vn) (sr.sr_typeof_exp))
`;

val P_entails_an_interpret_def = Define `
    P_entails_an_interpret sr P sys =
    (!s.
     (symb_concst_pc s = symb_symbst_pc sys) ==>
     (symb_concst_store_ty_sat sr (symb_symbst_store_ty sr sys) s) ==>
     (P s) ==>
     (?H. symb_matchstate sr sys H s))
`;

val Pi_overapprox_Q_def = Define `
    Pi_overapprox_Q sr P sys Pi Q =
    (!sys' s s' H.
     (sys' IN Pi) ==>
     (symb_concst_store_ty_sat sr (symb_symbst_store_ty sr sys) s) ==>
     (P s) ==>
     (symb_matchstate sr sys H s) ==>
     (symb_matchstate_ext sr sys' H s') ==>
     (Q s s'))
`;

val prop_holds_def = Define `
    prop_holds sr l L sty P Q =
    (!s.
     (symb_concst_pc s = l) ==>
     (symb_concst_store_ty_sat sr sty s) ==>
     (P s) ==>
     (?n s'.
       conc_step_n_in_L sr s n L s' /\
       Q s s'))
`;

val prop_holds_spec_def = Define `
    prop_holds_spec sr l L P Q =
    (!s.
     (symb_concst_pc s = l) ==>
     (P s) ==>
     (?n s'.
       conc_step_n_in_L sr s n L s' /\
       Q s s'))
`;


(*
GOAL: PROPERTY TRANSFER THEOREM
=======================================================
*)
val symb_prop_transfer_thm = store_thm(
   "symb_prop_transfer_thm", ``
!sr.
!sys L Pi P Q.
  (symb_symbols_f_sound sr) ==>
  (P_entails_an_interpret sr P sys) ==>
  (Pi_overapprox_Q sr P sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds sr (symb_symbst_pc sys) L (symb_symbst_store_ty sr sys) P Q)
``,
  REWRITE_TAC [P_entails_an_interpret_def, Pi_overapprox_Q_def, prop_holds_def, symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [symb_matchstate_TO_minimal_thm]
);

val symb_prop_spec_thm = store_thm(
   "symb_prop_spec_thm", ``
!sr l L sty P Q.
  (!s. P s ==> symb_concst_store_ty_sat sr sty s) ==>
  (prop_holds sr l L sty P Q) ==>
  (prop_holds_spec sr l L P Q)
``,
  REWRITE_TAC [prop_holds_def, prop_holds_spec_def] >>
  METIS_TAC []
);


(*
GOAL: PROPERTY TRANSFER COMPATIBILITY (BINARY HOARE LOGIC)
=======================================================
*)
local
  open abstract_hoare_logicTheory;
  open abstract_hoare_logicSimps;
in

(*
  it seems we can in principle produce contracts of all code fragments
  - unless the start label is in the end label set, because in this case the transition system could not "start"
  - unless it cannot be exhaustively symbolically executed, like if they contain unbound loops, or impractically largely bound loops
*)

val symb_hl_trs_def = Define `
  symb_hl_trs sr st = SOME (sr.sr_step_conc st)
`;

val symb_hl_weak_def = Define `
  symb_hl_weak sr st ls st' =
    (?n. (conc_step_n_in_L_relaxed sr st n (COMPL ls) st' /\ (~((symb_concst_pc st') IN (COMPL ls)))))
`;

val symb_hl_etl_wm_def =
  Define `symb_hl_etl_wm sr = <|
    trs  := symb_hl_trs sr;
    weak := symb_hl_weak sr;
    pc   := symb_concst_pc
  |>`;

val symb_prop_transfer_binHoare_thm = store_thm(
   "symb_prop_transfer_binHoare_thm", ``
!sr.
!Q' l L P Q.
  (Q' = \s. \s'. Q s' /\ (~((symb_concst_pc s') IN (COMPL L)))) ==>
  (prop_holds_spec sr l (COMPL L) P Q') ==>
  (abstract_jgmt (symb_hl_etl_wm sr) l L P Q)
``,
  REWRITE_TAC [prop_holds_spec_def, abstract_jgmt_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `ms`)) >>

  REV_FULL_SIMP_TAC (std_ss++bir_wm_SS) [symb_hl_etl_wm_def, symb_hl_weak_def] >>

  METIS_TAC [conc_step_n_in_L_IMP_relaxed_thm]
);

val symb_hl_trs_thm = store_thm(
   "symb_hl_trs_thm",
  ``!sr. !x. (symb_hl_trs sr x) = SOME (sr.sr_step_conc x)``,
  METIS_TAC [symb_hl_trs_def]
);

val FUNPOW_OPT_SOME_symb_hl_trs_thm = store_thm(
   "FUNPOW_OPT_SOME_symb_hl_trs_thm",
  ``!sr. !n x.
      (FUNPOW_OPT (symb_hl_trs sr) n x = SOME (FUNPOW sr.sr_step_conc n x))``,
  METIS_TAC [FUNPOW_OPT_SOME_thm, symb_hl_trs_thm]
);


val symb_hl_is_weak = store_thm(
   "symb_hl_is_weak",
  ``!sr.
      weak_model (symb_hl_etl_wm sr)``,
  SIMP_TAC (std_ss++bir_wm_SS) [weak_model_def, symb_hl_etl_wm_def, symb_hl_weak_def, symb_hl_trs_def] >>

  REWRITE_TAC [conc_step_n_in_L_relaxed_def, step_n_in_L_relaxed_def, step_n_in_L_thm, step_n_def, FUNPOW_OPT_SOME_symb_hl_trs_thm] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `n` >>

    (*`n > 0` by () >>*)
    FULL_SIMP_TAC std_ss [IN_COMPL, GREATER_DEF]
  )
);

end;

val _ = export_theory();
