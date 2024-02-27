open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

open arithmeticTheory;
open pred_setTheory;

val _ = new_theory "symb_rules";


(*
GOAL: INFERENCE RULES
=======================================================
*)

(* ************************* *)
(*        RULE AUX           *)
(* ************************* *)

(* this is a generic theorem for rules that replace a symbolic state in Pi *)
val symb_rule_TRANSF_GEN_thm = store_thm(
   "symb_rule_TRANSF_GEN_thm", ``
!sr.
!sys L Pi sys2 sys2'.
  (!H s s'.
     (symb_minimal_interpretation sr sys H) ==>
     (symb_matchstate sr sys H s) ==>
(*
     (symb_interpr_ext H' H) ==>
     (symb_matchstate sr sys2 H' s') ==>
*)
     (symb_matchstate_ext sr sys2 H s') ==>
     (symb_matchstate_ext sr sys2' H s')
  ) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [] >>
(* symb_matchstate_ext_def *)

  Cases_on `sys' = sys2` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ] >>

  (* the case when we would execute to sys2 *)
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Q.EXISTS_TAC `sys2'` >>
  ASM_SIMP_TAC std_ss [] >>

  METIS_TAC []
);
val symb_rule_TRANSF_GEN2_thm = store_thm(
   "symb_rule_TRANSF_GEN2_thm", ``
!sr.
!sys L Pi sys2 sys2s.
  (!H s s'.
     (symb_minimal_interpretation sr sys H) ==>
     (symb_matchstate sr sys H s) ==>
(*
     (symb_interpr_ext H' H) ==>
     (symb_matchstate sr sys2 H' s') ==>
*)
     (symb_matchstate_ext sr sys2 H s') ==>
     (?sys2'. (sys2' IN sys2s) /\ symb_matchstate_ext sr sys2' H s')
  ) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION sys2s))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [] >>
(* symb_matchstate_ext_def *)

  Cases_on `sys' = sys2` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ] >>

  (* the case when we would execute to sys2 *)
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  FULL_SIMP_TAC std_ss [] >>

  PAT_X_ASSUM ``!x. A`` IMP_RES_TAC >>

  METIS_TAC []
);

(* ************************* *)
(*        RULE STEP          *)
(* ************************* *)
val symb_rule_STEP_thm = store_thm(
   "symb_rule_STEP_thm", ``
!sr.
!sys L Pi.
  (symb_step_sound sr) ==>
  (sr.sr_step_symb sys = Pi) ==>
  ((symb_symbst_pc sys) IN L) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_step_sound_def, symb_matchstate_ext_def, symb_hl_step_in_L_sound_def, conc_step_n_in_L_def, step_n_in_L_thm] >>
  REPEAT STRIP_TAC >>

  Q.EXISTS_TAC `SUC 0` >>
  Q.EXISTS_TAC `sr.sr_step_conc s` >>

  SIMP_TAC arith_ss [step_n_def, FUNPOW] >>
  METIS_TAC [symb_interpr_ext_id_thm, symb_matchstate_def]
);


(* ************************* *)
(*         RULE SEQ          *)
(* ************************* *)
val symb_SEQ_interpr_dom_INTER_thm = store_thm(
   "symb_SEQ_interpr_dom_INTER_thm", ``
!sr.
!sys_A sys_B Pi_B sys_Pi_B H1 H2 H3 sys s.
  ((symb_symbols sr sys_A)
   INTER
   ((symb_symbols_set sr Pi_B) DIFF (symb_symbols sr sys_B))
   = EMPTY) ==>

  (sys_Pi_B IN Pi_B) ==>

  (symb_minimal_interpretation sr sys_A H1) ==>
  (symb_minimal_interpretation sr sys_B H2) ==>
  (symb_minimal_interpretation sr sys_Pi_B H3) ==>

  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY)
``,
  METIS_TAC [symb_minimal_interpretation_EQ_dom_thm,
             symb_symbols_set_SUBSET_thm, bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm, SUBSET_of_DIFF_thm]
);

(* TODO: split this into two *)
val symb_rule_SEQ_thm = store_thm(
   "symb_rule_SEQ_thm", ``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment B that have been lost in A *)
  (((symb_symbols sr sys_A) (* DIFF (symb_symbols sr sys_B) *))
       INTER ((symb_symbols_set sr Pi_B) DIFF (symb_symbols sr sys_B))
   = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (symb_hl_step_in_L_sound sr (sys_B, L_B, Pi_B)) ==>
  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, (Pi_A DIFF {sys_B}) UNION Pi_B))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def, conc_step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys_A H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* the case when after A we don't execute through sys_B *)
  Cases_on `sys' = sys_B` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC [step_n_in_L_IMP_SUPER_thm, SUBSET_UNION]
  ] >>

  (* the case when after A we actually execute through sys_B *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys_B`, `H'`, `s'`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* execute from s' (sys') with fragment B *)
  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys_B H ==> A`` (ASSUME_TAC o (Q.SPECL [`s'`, `H''`])) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* the sequential complete composition to the state after executing in B *)
  Q.EXISTS_TAC `n+n'` >> Q.EXISTS_TAC `s''` >>
  STRIP_TAC >- (
    METIS_TAC [step_n_in_L_SEQ_thm]
  ) >>

  (* establish the properties for the reached state *)
  Q.EXISTS_TAC `sys''` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  (* construct the interpretation where all lost symbols in A are
     mapped as initially and prove it to extend the initial interpretation *)
  rename1 `symb_matchstate sr sys'' H_f s''` >>

  (* first, make H_f minimal w.r.t. sys'' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys''`, `H_f`, `s''`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys_B H_i` >>
  rename1 `symb_minimal_interpretation sr sys'' H_e` >>

  (* we can conlude that this intersection is empty *)
  `(symb_interpr_dom H) INTER ((symb_interpr_dom H_e) DIFF (symb_interpr_dom H_i)) = EMPTY` by (
    METIS_TAC [symb_SEQ_interpr_dom_INTER_thm]
  ) >>

  (* don't forget about carrying along well-typedness *)
  `symb_interpr_welltyped sr H` by (
    METIS_TAC [symb_matchstate_def]
  ) >>

  (* we can construct an interpretation that both matches this symbolic state
     with the concrete final state and is an extension of the initial interpretation *)
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm, symb_matchstate_ext_def]
);


(* ************************* *)
(*         RULE INF          *)
(* ************************* *)
val symb_pcondinf_def = Define `
    symb_pcondinf sr pcond =
  (!H.
    (symb_interpr_welltyped sr H) ==>
    (symb_interpr_for_symbs (sr.sr_symbols_f pcond) H) ==>
    (sr.sr_interpret_f H pcond <> SOME sr.sr_val_true)
  )
`;



val symb_rule_INF_thm = store_thm(
   "symb_rule_INF_thm", ``
!sr.
!sys L Pi sys'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>

  (symb_pcondinf sr (symb_symbst_pcond sys')) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi DIFF {sys'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_matchstate_ext_def] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `sys' = sys''` >- (
    `(symb_interpr_for_symbs (sr.sr_symbols_f (symb_symbst_pcond sys')) H')` by (
      METIS_TAC [symb_suitable_interpretation_def, SUBSET_TRANS,
        symb_interpr_for_symbs_def, symb_symbols_SUBSET_pcond_thm]
    ) >>

    METIS_TAC [symb_pcondinf_def, symb_interpr_symbpcond_def]
  ) >>

  METIS_TAC []
);


(* ************************* *)
(*        RULE CONS          *)
(* ************************* *)
val symb_pcondwiden_def = Define `
    symb_pcondwiden sr pcond pcond' =
    (!H.
      (symb_interpr_welltyped sr H) ==>
      (symb_interpr_for_symbs ((sr.sr_symbols_f pcond) UNION (sr.sr_symbols_f pcond')) H) ==>
      (sr.sr_interpret_f H pcond = SOME sr.sr_val_true) ==>
      (sr.sr_interpret_f H pcond' = SOME sr.sr_val_true))
`;

val symb_pcondwiden_sys_def = Define `
    symb_pcondwiden_sys sr sys sys' = (
    (symb_symbst_extra sys =
     symb_symbst_extra sys') /\
    (symb_symbst_pc sys =
     symb_symbst_pc sys') /\
    (symb_symbst_store sys =
     symb_symbst_store sys') /\
    (symb_pcondwiden sr (symb_symbst_pcond sys) (symb_symbst_pcond sys'))
  )
`;

val symb_pcondwiden_sys_matchstate_IMP_matchstate_thm = store_thm(
   "symb_pcondwiden_sys_matchstate_IMP_matchstate_thm", ``
!sr.
!sys sys' H s.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_pcondwiden_sys sr sys sys') ==>
  (symb_matchstate sr sys H s) ==>

  (symb_matchstate sr sys' (symb_interpr_extend_symbs_sr sr (symb_symbols sr sys') H) s)
``,
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `H' = (symb_interpr_extend_symbs_sr sr (symb_symbols sr sys') H)` >>

  `symb_interpr_welltyped sr H'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_welltyped_thm, symb_matchstate_def]
  ) >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm, symb_interpr_extend_symbs_IMP_ext_thm,
        symb_interpr_extend_symbs_sr_def]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm, symb_interpr_extend_symbs_sr_def,
         symb_suitable_interpretation_SUBSET_dom_thm, symb_matchstate_def]
       @[symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION])
  ) >>

  `symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION (sr.sr_symbols_f (symb_symbst_pcond sys'))) H'` by (
    METIS_TAC
      [symb_interpr_for_symbs_def, symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION]
  ) >>

  `symb_suitable_interpretation sr sys' H'` by (
    METIS_TAC [symb_suitable_interpretation_def, symb_interpr_for_symbs_def, SUBSET_TRANS, SUBSET_UNION]
  ) >>

  FULL_SIMP_TAC std_ss [symb_pcondwiden_sys_def, symb_pcondwiden_def, symb_matchstate_def] >>

  METIS_TAC [symb_interpr_symbpcond_def]
);

val symb_pcondwiden_sys_matchstate_IMP_matchstate_EXISTS_thm = store_thm(
   "symb_pcondwiden_sys_matchstate_IMP_matchstate_EXISTS_thm", ``
!sr.
!sys1 sys2 s H1 H2.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_pcondwiden_sys sr sys1 sys2) ==>

  (symb_matchstate sr sys1 H1 s) ==>
  (?H2.
    (symb_interpr_ext H2 H1) /\
    (symb_matchstate sr sys2 H2 s))
``,
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `symb_interpr_extend_symbs_sr sr (symb_symbols sr sys2) H1` >>

  FULL_SIMP_TAC std_ss [symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_ext_thm] >>

  METIS_TAC [symb_interpr_extend_symbs_sr_def, symb_pcondwiden_sys_matchstate_IMP_matchstate_thm]
);

(* TODO: split this into two *)
val symb_rule_CONS_S_thm = store_thm(
   "symb_rule_CONS_S_thm", ``
!sr.
!sys' sys L Pi.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr Pi) DIFF (symb_symbols sr sys')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys', L, Pi)) ==>
  (symb_pcondwiden_sys sr sys sys') ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  rename1 `symb_minimal_interpretation sr sys H1` >>

  (* extend H to include arbitrary mappings for everything missing w.r.t. sys',
       this is like the other rule CONS_E *)
  (* Q.ABBREV_TAC `H_a = symb_interpr_extend_symbs (symb_symbols sr sys') H1` >> *)
  (* this can now match sys' with s *)
  IMP_RES_TAC symb_pcondwiden_sys_matchstate_IMP_matchstate_EXISTS_thm >>
  rename1 `symb_matchstate sr sys' H_a s` >>

  (* then get a minimal interpretation for sys' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys'`, `H_a`, `s`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys' H2` >>

  (* then execute *)
  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`s`, `H2`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  STRIP_TAC >- (
    METIS_TAC [step_n_in_L_SEQ_thm]
  ) >>
  rename1 `symb_matchstate sr sys'' H_b s'` >>

  (* establish the properties for the reached state *)
  Q.EXISTS_TAC `sys''` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  (* must make H_b minimal w.r.t. sys'' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys''`, `H_b`, `s'`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys'' H3` >>

  (* extend the interpretation with mappings from the original H
       to get an extension from H that can match the state,
       this is like in the sequential composition proof *)
  (* finally relate the final interpretation back to the initial state *)
  `(symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY` by (
    METIS_TAC [symb_SEQ_interpr_dom_INTER_thm]
  ) >>
  `symb_interpr_welltyped sr H1` by (
    METIS_TAC [symb_matchstate_def]
  ) >>
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm, symb_matchstate_ext_def]
);

val symb_pcondwiden_sys_TRANSF_matchstate_ext_thm = store_thm(
   "symb_pcondwiden_sys_TRANSF_matchstate_ext_thm", ``
!sr.
!sys sys2 sys2'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_pcondwiden_sys sr sys2 sys2') ==>

!H s s'.
  (symb_minimal_interpretation sr sys H) ==>
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  (symb_matchstate_ext sr sys2' H s')
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* have to proof that we can match with an extension of H for sys' *)
  (* start with H', rename to H_m *)
  rename1 `symb_matchstate sr sys2 H_m s'` >>
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs_sr sr (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm,
      symb_interpr_extend_symbs_sr_def]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_pcondwiden_sys_matchstate_IMP_matchstate_thm]
);


val symb_rule_CONS_E_thm = store_thm(
   "symb_rule_CONS_E_thm", ``
!sr.
!sys L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_pcondwiden_sys sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_pcondwiden_sys_TRANSF_matchstate_ext_thm]
);

val symb_rule_CONS_thm = store_thm(
   "symb_rule_CONS_thm", ``
!sr.
!sys1' sys1 L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys1) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr Pi) DIFF (symb_symbols sr sys1')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys1', L, Pi)) ==>
  (symb_pcondwiden_sys sr sys1 sys1') ==>
  (symb_pcondwiden_sys sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys1, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_CONS_S_thm, symb_rule_CONS_E_thm]
);


(* ************************* *)
(*        RULE SUBST         *)
(* ************************* *)
val symb_simplification_def = Define `
    symb_simplification sr pcond symbexp symbexp' =
    (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs
            ((sr.sr_symbols_f pcond) UNION
             (sr.sr_symbols_f symbexp) UNION
             (sr.sr_symbols_f symbexp')) H) ==>

       (sr.sr_interpret_f H pcond = SOME sr.sr_val_true) ==>
       (sr.sr_interpret_f H symbexp = sr.sr_interpret_f H symbexp')
    )
`;

val symb_simplification_matchstate_IMP_matchstate_thm = store_thm(
   "symb_simplification_matchstate_IMP_matchstate_thm", ``
!sr.
!var symbexp symbexp' sys sys' H H' s.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_simplification sr (symb_symbst_pcond sys) symbexp symbexp') ==>
  (symb_symbst_store_update var symbexp' sys = sys') ==>

  (symb_matchstate sr sys H s) ==>

  ((symb_interpr_extend_symbs_sr sr (symb_symbols sr sys') H) = H') ==>

  (symb_matchstate sr sys' H' s)
``,
  REPEAT STRIP_TAC >>

  `symb_interpr_welltyped sr H'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_welltyped_thm, symb_matchstate_def]
  ) >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm,
      symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_extend_symbs_sr_def]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm, symb_interpr_extend_symbs_sr_def,
         symb_suitable_interpretation_SUBSET_dom_thm, symb_matchstate_def]
       @[symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION])
  ) >>

  `symb_interpr_for_symbs
              (sr.sr_symbols_f (symb_symbst_pcond sys) UNION
               sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp') H'` by (
    METIS_TAC
      [symb_interpr_for_symbs_def, UNION_SUBSET, SUBSET_TRANS,
       symb_symbols_SUBSET_store_exps_thm2,
       symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2,
       symb_symbols_SUBSET_pcond_thm]
  ) >>

  `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp' SUBSET
       symb_interpr_dom H'` by (
    METIS_TAC [symb_interpr_for_symbs_def, SUBSET_UNION, SUBSET_TRANS, UNION_ASSOC]
  ) >>

  `symb_interpr_symbpcond sr H' sys` by (
    METIS_TAC
      [symb_matchstate_def]
  ) >>

  METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm, symb_simplification_def, symb_interpr_symbpcond_def]
);

val symb_simplification_TRANSF_matchstate_ext_thm = store_thm(
   "symb_simplification_TRANSF_matchstate_ext_thm", ``
!sr.
!sys sys2 sys2' var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr (symb_symbst_pcond sys2) symbexp symbexp') ==>
  (sys2' = symb_symbst_store_update var symbexp' sys2) ==>

!H s s'.
  (symb_minimal_interpretation sr sys H) ==>
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  (symb_matchstate_ext sr sys2' H s')
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* have to proof that we can match with an extension of H for sys' *)
  (* start with H', rename to H_m *)
  rename1 `symb_matchstate sr sys' H_m s'` >>
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs_sr sr (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm,
      symb_interpr_extend_symbs_sr_def]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_simplification_matchstate_IMP_matchstate_thm]
);

val symb_rule_SUBST_thm = store_thm(
   "symb_rule_SUBST_thm", ``
!sr.
!sys L Pi sys2 sys2' var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr (symb_symbst_pcond sys2) symbexp symbexp') ==>
  (sys2' = symb_symbst_store_update var symbexp' sys2) ==>

  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_simplification_TRANSF_matchstate_ext_thm]
);


(* ************************* *)
(*        RULE FRESH         *)
(* ************************* *)
val symb_fresh_simplification_matchstate_IMP_matchstate_thm = store_thm(
   "symb_fresh_simplification_matchstate_IMP_matchstate_thm", ``
!sr.
!var symb symb_exp symbexp symbexp' sys sys' H H' s.
  (symb_symbols_f_sound sr) ==>
  (symb_typeof_exp_sound sr) ==>
  (symb_val_eq_sound sr) ==>
  (symb_mk_exp_eq_f_sound sr) ==>
  (symb_mk_exp_conj_f_sound sr) ==>
  (symb_mk_exp_symb_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb NOTIN symb_interpr_dom H) ==>
  (symb NOTIN symb_symbols sr sys) ==>
  (sr.sr_symbols_f symb_exp SUBSET symb_interpr_dom H) ==> (* TODO: maybe don't need this assumption? but it seems like we do, otherwise need other assumptions (like symb NOTIN symb_exp) and the proof will be more complicated *)

  (sr.sr_typeof_exp symb_exp = SOME (sr.sr_typeof_symb symb)) ==>

  (*(symb_interpr_welltyped sr H) ==> *) (* we have this in symb_matchstate sr sys H s *)

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symb_exp)
     (symb_symbst_store_update var symbexp' sys)
   = sys'
  ) ==>

  (symb_simplification sr (symb_symbst_pcond sys') symbexp symbexp') ==>


  (symb_matchstate sr sys H s) ==>

  ((symb_interpr_extend_symbs_sr sr (symb_symbols sr sys') (symb_interpr_update H (symb, sr.sr_interpret_f H symb_exp))) = H') ==>

  (symb_matchstate sr sys' H' s /\
   symb_interpr_ext H' H)
``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>

  `symb_interpr_ext H' H` by (
    Q.ABBREV_TAC `H2 = symb_interpr_update H (symb,sr.sr_interpret_f H symb_exp)` >>
    `symb_interpr_ext H2 H` by (
    (* note: symb ∉ symb_interpr_dom H, so it doesn't matter if sr.sr_interpret_f H symb_exp is SOME or NONE, but it should evaluate to SOME  *)
      METIS_TAC [symb_interpr_ext_UPDATE_thm]
    ) >>

    METIS_TAC [symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm]
  ) >>
  ASM_REWRITE_TAC [] >>

  `symb NOTIN sr.sr_symbols_f symb_exp` by (
    (* because symb ∉ symb_interpr_dom H, and sr.sr_symbols_f symb_exp ⊆ symb_interpr_dom H *)
    METIS_TAC [SUBSET_THM]
  ) >>

  `?v. sr.sr_interpret_f H symb_exp = SOME v /\ sr.sr_typeof_val v = sr.sr_typeof_symb symb` by (
    METIS_TAC [symb_typeof_exp_sound_def, symb_matchstate_def]
  ) >>

  `symb_interpr_welltyped sr H'` by (
    `symb_interpr_welltyped sr H` by (
      METIS_TAC [symb_matchstate_def]
    ) >>
    METIS_TAC [symb_interpr_update_interpret_f_IMP_welltyped_thm, symb_interpr_extend_symbs_sr_IMP_welltyped_thm, symb_matchstate_def]
  ) >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>

    STRIP_TAC >- (
      METIS_TAC [matchstate_IMP_symbols_SUBSET_interpr_dom_thm, symb_interpr_ext_def,
                 symb_interpr_ext_IMP_dom_thm, SUBSET_TRANS]
    ) >>

    (*
    what if symb is in sys', for example in symbexp'?
    no problem if we can establish that sr.sr_interpret_f H symb_exp evaluates to SOME
    ... this is not even needed because we first update H with symb, and then extend it to make sure the symbols of sys' are all there
    *)
    Q.ABBREV_TAC `H2 = symb_interpr_update H (symb, SOME v)` >>
    METIS_TAC
      [symb_interpr_extend_symbs_IMP_for_symbs_thm, symb_interpr_extend_symbs_sr_def,
         symb_interpr_for_symbs_def, UNION_SUBSET]
  ) >>

  Q.ABBREV_TAC `pcond_f = symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symb_exp` >>
  `symb_interpr_for_symbs
              (sr.sr_symbols_f (pcond_f (symb_symbst_pcond sys)) UNION
               sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp') H'` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET, symb_interpr_for_symbs_def] >>
    (* the symbols are in sys and sys', in the stores and in the precond of sys' *)
    `symb_symbst_pcond sys' = pcond_f (symb_symbst_pcond sys)` by (
      METIS_TAC [symb_symbst_store_update_UNCHANGED_thm, symb_symbst_pcond_update_READ_thm]
    ) >>

    `symb_symbst_store sys' var = SOME symbexp'` by (
      Cases_on `sys` >>
      Cases_on `sys'` >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
        [symb_symbst_store_update_def, symb_symbols_def,
         symb_symbst_store_def, symb_symbols_store_def,
         symb_symbst_pcond_update_def, symb_symbst_t_11] >>

      METIS_TAC [combinTheory.APPLY_UPDATE_THM]
    ) >>

    METIS_TAC [symb_symbols_SUBSET_pcond_thm, symb_symbols_SUBSET_store_thm, symb_symbols_SUBSET_store_exps_thm, SUBSET_TRANS]
  ) >>

  (* from symb_matchstate sr sys H' s, path cond of sys is true *)
  `sr.sr_interpret_f H' (symb_symbst_pcond sys) = SOME sr.sr_val_true` by (
    METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def]
  ) >>

  `sr.sr_interpret_f H' (pcond_f (symb_symbst_pcond sys)) = SOME sr.sr_val_true` by (
    (* and symb_exp evaluates to true and the same like lookup of symb in H' *)
    `sr.sr_interpret_f H' (sr.sr_mk_exp_symb_f symb) = SOME v` by (
      `symb_interpr_get H' symb = SOME v` by (
        FULL_SIMP_TAC std_ss [] >>
        Q.ABBREV_TAC `H2 = symb_interpr_update H (symb,SOME v)` >>
        `symb_interpr_get H2 symb = SOME v` by (
          METIS_TAC [symb_interpr_get_update_id_thm]
        ) >>

        METIS_TAC [symb_interpr_extend_symbs_IMP_get_thm, symb_interpr_extend_symbs_sr_def]
      ) >>
      METIS_TAC [symb_mk_exp_symb_f_sound_def]
    ) >>
    `sr.sr_interpret_f H' symb_exp = SOME v` by (
      cheat (*  *)
    ) >>

    Q.UNABBREV_TAC `pcond_f` >>
    FULL_SIMP_TAC std_ss [symb_expr_conj_eq_thm, symb_val_eq_sound_def]
  ) >>


(*
  `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp' SUBSET
       symb_interpr_dom H'` by (
    METIS_TAC [symb_interpr_for_symbs_def, SUBSET_UNION, SUBSET_TRANS, UNION_ASSOC]
  ) >>
*)

  `sr.sr_interpret_f H' symbexp = sr.sr_interpret_f H' symbexp'` by (
    PAT_X_ASSUM ``symb_symbst_pcond_update A  B = C`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [symb_symbst_store_update_UNCHANGED_thm, symb_symbst_pcond_update_READ_thm] >>
    METIS_TAC [symb_simplification_def]
  ) >>

  Q.ABBREV_TAC `sys2 = symb_symbst_store_update var symbexp' sys` >>
  `symb_symbst_pcond sys = symb_symbst_pcond sys2` by (
    METIS_TAC [symb_symbst_store_update_UNCHANGED_thm]
  ) >>

  `symb_matchstate sr sys2 H' s` by (
    `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp' SUBSET
         symb_interpr_dom H'` by (
      METIS_TAC [symb_interpr_for_symbs_def, SUBSET_UNION, SUBSET_TRANS, UNION_ASSOC]
    ) >>
    METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm, symb_interpr_symbpcond_def]
  ) >>

  `sr.sr_interpret_f H' (symb_symbst_pcond sys2) = sr.sr_interpret_f H' (pcond_f (symb_symbst_pcond sys2))` by (
    METIS_TAC []
  ) >>

  `sr.sr_symbols_f (symb_symbst_pcond sys2) UNION
   sr.sr_symbols_f (pcond_f (symb_symbst_pcond sys2))
   SUBSET symb_interpr_dom H'` by (
    METIS_TAC [symb_interpr_for_symbs_def, UNION_SUBSET, SUBSET_TRANS, symb_symbols_SUBSET_pcond_thm]
  ) >>

  METIS_TAC [symb_symbst_pcond_update_IMP_matchstate_EQ_thm]
);


 (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
 (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
 (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
 (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
 (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
val symb_FRESH_simplification_TRANSF_matchstate_ext_thm = store_thm(
   "symb_FRESH_simplification_TRANSF_matchstate_ext_thm", ``
!sr.
!sys sys2 sys2' var symb_exp symb symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_typeof_exp_sound sr) ==>
  (symb_val_eq_sound sr) ==>
  (symb_mk_exp_eq_f_sound sr) ==>
  (symb_mk_exp_conj_f_sound sr) ==>
  (symb_mk_exp_symb_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb NOTIN symb_symbols sr sys ) ==>
  (symb NOTIN symb_symbols sr sys2) ==>

(*
for this theorem, and using the theorem above, it should be sufficient to require symb NOTIN symbols of symb_exp, then we can extend the interpretation for all the symbols in symb_exp
*)
  (sr.sr_symbols_f symb_exp SUBSET symb_symbols sr sys UNION symb_symbols sr sys2) ==>

  (sr.sr_typeof_exp symb_exp = SOME (sr.sr_typeof_symb symb)) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symb_exp)
     (symb_symbst_store_update var symbexp' sys2)
   = sys2'
  ) ==>

  (symb_simplification sr (symb_symbst_pcond sys2') symbexp symbexp') ==>

!H s s'.
  (symb_minimal_interpretation sr sys H) ==>
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  (symb_matchstate_ext sr sys2' H s')
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* from H', make an H_e restricted to the symbols of sys and sys2 *)
  (* this is an extension from H *)
  `?H_e. symb_interpr_ext H_e H /\
         symb NOTIN symb_interpr_dom H_e /\
         symb_matchstate sr sys2 H_e s' /\
         sr.sr_symbols_f symb_exp SUBSET symb_interpr_dom H_e` by (
    Q.ABBREV_TAC `syssymbs = symb_symbols sr sys UNION symb_symbols sr sys2` >>
    Q.ABBREV_TAC `H_e = symb_interpr_restr syssymbs H'` >>
    Q.EXISTS_TAC `H_e` >>
    (* H_e is equal to H' for all symbols of sys and sys2, and has all symbols of sys and sys2 *)
    `symb_interprs_eq_for H' H_e syssymbs` by (
      METIS_TAC [symb_interpr_restr_IS_eq_for_thm]
    ) >>
    `symb_interpr_dom H_e = syssymbs` by (
      `symb_interpr_dom H' INTER syssymbs = syssymbs` by (
        `syssymbs SUBSET symb_interpr_dom H'` by (
          (* via matchstate and interpr_ext dom subsets *)
          Q.UNABBREV_TAC `syssymbs` >>
          REWRITE_TAC [UNION_SUBSET] >>

          METIS_TAC [matchstate_IMP_symbols_SUBSET_interpr_dom_thm,
               symb_interpr_ext_IMP_dom_thm, SUBSET_TRANS]
        ) >>

        REWRITE_TAC [FUN_EQ_THM] >>
        METIS_TAC [INTER_applied, IN_APP, SUBSET_applied]
      ) >>

      METIS_TAC [symb_interpr_restr_dom_thm, INTER_UNION]
    ) >>

    (* because has all symbols, also the symbols of symb_exp are included *)
    `sr.sr_symbols_f symb_exp SUBSET symb_interpr_dom H_e` by (
      METIS_TAC [](*SUBSET_TRANS]*)
    ) >>
    (* symb is in neither states' symbol set *)
    `symb NOTIN symb_interpr_dom H_e` by (
      METIS_TAC [IN_UNION]
    ) >>
    ASM_SIMP_TAC std_ss [] >>

    (* H is minimal in sys, therefore equal for all symbols of sys makes it an ext *)
    `symb_interpr_ext H_e H` by (
      `symb_interprs_eq_for H H_e ((symb_interpr_dom H) INTER (symb_interpr_dom H_e))` by (
        METIS_TAC [symb_interpr_restr_ext_thm, symb_interpr_ext_IMP_interprs_eq_for_INTER_thm, symb_interprs_eq_for_INTER_def]
      ) >>
      `(symb_interpr_dom H) INTER (symb_interpr_dom H_e) = (symb_interpr_dom H)` by (
        (* domain of H is exactly sys, because of minimal_interpr sys H *)
        METIS_TAC [INTER_UNION, symb_minimal_interpretation_EQ_dom_thm]
      ) >>
      FULL_SIMP_TAC std_ss [] >>

      METIS_TAC [symb_interpr_ext_def, symb_interprs_eq_for_COMM_thm]
    ) >>
    ASM_SIMP_TAC std_ss [] >>

    (* match sys2 because H_e is equal for all symbols of this state, modify: symb_matchstate_TO_min_RESTR_thm *)
    METIS_TAC [symb_matchstate_TO_min_RESTR_UNION_thm, UNION_COMM]
  ) >>

  (* have to proof that we can match with an extension of H for sys2' *)
  Q.ABBREV_TAC `H_m = symb_interpr_extend_symbs_sr sr (symb_symbols sr sys2') (symb_interpr_update H_e (symb, sr.sr_interpret_f H_e symb_exp))` >>
  Q.EXISTS_TAC `H_m` >>

  `symb_interpr_ext H_m H_e /\ symb_matchstate sr sys2' H_m s'` by (
    METIS_TAC [symb_fresh_simplification_matchstate_IMP_matchstate_thm]
  ) >>

  METIS_TAC [symb_interpr_ext_TRANS_thm]
);

(* rule to introduce fresh symbols as values of store variables
     (as abbreviations or as first step of forgetting values) *)
val symb_rule_FRESH_thm = store_thm(
   "symb_rule_FRESH_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_typeof_exp_sound sr) ==>
(symb_val_eq_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>

(!sys L Pi sys2 sys2' var symb_exp symb symbexp symbexp'.
  (* the symbol has to be fresh where it matters *)
  (~(symb IN symb_symbols sr sys )) ==>
  (~(symb IN symb_symbols sr sys2)) ==>
  (* and the abbreviated expression must only use symbols that are already in sys2 *)
  (sr.sr_symbols_f symb_exp SUBSET symb_symbols sr sys2) ==> (* TODO: maybe don't need this assumption? check this! *)

  (* the symbol we choose has to be associated with the right type *)
  (sr.sr_typeof_exp symb_exp = SOME (sr.sr_typeof_symb symb)) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symb_exp)
     (symb_symbst_store_update var symbexp' sys2)
   = sys2'
  ) ==>

  (symb_simplification sr (symb_symbst_pcond sys2') symbexp symbexp') ==>

  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
)
``,
  REPEAT STRIP_TAC >>

  `sr.sr_symbols_f symb_exp SUBSET symb_symbols sr sys UNION symb_symbols sr sys2` by (
    METIS_TAC [SUBSET_applied, UNION_applied, IN_APP]
  ) >>

  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_FRESH_simplification_TRANSF_matchstate_ext_thm]
);


(* ************************* *)
(*        RULE INST          *)
(* ************************* *)
val symb_matchstate_UPDATE_indep_thm = store_thm(
   "symb_matchstate_UPDATE_indep_thm", ``
!sr.
!sys s symb v H H'.
  (symb_symbols_f_sound sr) ==>

  (* we need this assumption because an instantiation only in the reachable states requires some assumption that guarantees to not loose concrete states *)
  (~(symb IN symb_symbols sr sys)) ==>

  (sr.sr_typeof_val v = sr.sr_typeof_symb symb) ==>
  (H' = symb_interpr_update H (symb,SOME v)) ==>
  (symb_matchstate sr sys H  s) ==>
  (symb_matchstate sr sys H' s)
``,
  REPEAT STRIP_TAC >>
  `symb_interpr_welltyped sr H` by (
    METIS_TAC [symb_matchstate_def]
  ) >>
  `symb_interpr_welltyped sr H'` by (
    METIS_TAC [symb_matchstate_def, symb_interpr_update_SOME_IMP_welltyped_thm]
  ) >>
  `symb_symbols sr sys DELETE symb = symb_symbols sr sys` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
    METIS_TAC []
  ) >>
  `symb_interprs_eq_for H H' (symb_symbols sr sys)` by (
    METIS_TAC [symb_interprs_eq_for_update_thm, symb_interprs_eq_for_ID_thm]
  ) >>
  METIS_TAC [symb_interprs_eq_for_matchstate_IMP_matchstate_thm]
);
val symb_interprs_eq_for_INST_thm = store_thm(
   "symb_interprs_eq_for_INST_thm", ``
!sr.
!symb symbs sys1mbs sys2mbs H H_2 H_4 H_5.
  (symb_interprs_eq_for H H_2 (symbs DELETE symb)) ==>
  (symb_interprs_eq_for H_2 H_4 ((symbs DELETE symb) INTER sys1mbs)) ==>
  (symb_interpr_dom H_4 = sys1mbs UNION sys2mbs UNION {symb}) ==>

  ((symbs DELETE symb) INTER (sys2mbs DIFF sys1mbs) = EMPTY) ==>

  (H_5 = symb_interpr_extend H H_4) ==> (* means that H_5 is like H for all (sys1mbs UNION sys2mbs) *)

  (symb_interprs_eq_for H H_5 (symbs DELETE symb))
``,
    REWRITE_TAC [symb_interprs_eq_for_def] >>
    REPEAT STRIP_TAC >>

    rename1 `x IN symbs DELETE symb` >>
    Cases_on `x IN sys1mbs` >- (
      FULL_SIMP_TAC std_ss [symb_interprs_eq_for_def] >>
      `x IN (symbs DELETE symb) INTER sys1mbs` by (
        METIS_TAC [IN_INTER]
      ) >>
      `x IN symb_interpr_dom H_4` by (
        METIS_TAC [IN_UNION]
      ) >>
      METIS_TAC [symb_interpr_get_extend_dom_thm2]
    ) >>

    `~(x IN symb_interpr_dom H_4)` by (
      `~(x IN sys2mbs UNION {symb})` by (
        CCONTR_TAC >>
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
        (*REPEAT (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `x`)) >>*)
        METIS_TAC []
      ) >>
      METIS_TAC [IN_UNION]
    ) >>
    METIS_TAC [symb_interpr_get_extend_dom_thm2]
);

val symb_symbols_set_INTER_EMPTY_INST_thm = store_thm(
   "symb_symbols_set_INTER_EMPTY_INST_thm", ``
!symbs symb sr Pi sys1mbs sys2mbs sys'.
  (symbs INTER (symb_symbols_set sr Pi DIFF sys1mbs) = EMPTY) ==>
  (sys2mbs = symb_symbols sr sys') ==>
  (sys' IN Pi) ==>
  ((symbs DELETE symb) INTER (sys2mbs DIFF sys1mbs) = EMPTY)
``,
  REPEAT STRIP_TAC >>
  `sys2mbs SUBSET symb_symbols_set sr Pi` by (
    METIS_TAC [symb_symbols_set_SUBSET_thm]
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
  GEN_TAC >>
  REPEAT (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `x`)) >>
  METIS_TAC [SUBSET_DEF]
);



val symb_rule_INST_thm = store_thm(
   "symb_rule_INST_thm", ``
!sr.
!sys L Pi symb symb_inst.
  (symb_typeof_exp_sound sr) ==>
  (symb_subst_f_sound sr) ==>
  (symb_symbols_f_sound sr) ==>

  (* can we not prove that this rule also works if symb is not IN sys?
     or do we need to add an assumption on substitution that expressions stay unchanged in this case? *)
  (symb IN symb_symbols sr sys) ==>
  (sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb)) ==>

  (* exclude the freshly introduced symbols between sys and Pi in the expression symb_inst *)
  ((sr.sr_symbols_f symb_inst) INTER ((symb_symbols_set sr Pi) DIFF (symb_symbols sr sys)) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (symb_subst sr (symb, symb_inst) sys, L, symb_subst_set sr (symb, symb_inst) Pi))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def, conc_step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `sys_s = symb_subst sr (symb,symb_inst) sys` >>
  Q.ABBREV_TAC `Pi_s = symb_subst_set sr (symb,symb_inst) Pi` >>

  `symb_symbols sr sys_s = ((symb_symbols sr sys) DIFF {symb}) UNION sr.sr_symbols_f symb_inst` by (
    Q.UNABBREV_TAC `sys_s` >>
    FULL_SIMP_TAC std_ss [symb_subst_symbols_thm]
  ) >>

  `sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H` by (
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def, UNION_SUBSET]
  ) >>
  `?v. sr.sr_interpret_f H symb_inst = SOME v /\ sr.sr_typeof_val v = sr.sr_typeof_symb symb` by (
    METIS_TAC [symb_matchstate_def, symb_typeof_exp_sound_def]
    (* expression has type, H is well typed, H has all symbols of symb_inst (because symb is in sys and thus sys_s has symb_inst inside, and all symbols of sys_s are in H) *)
  ) >>

  Q.ABBREV_TAC `H_2 = symb_interpr_update H (symb,SOME v)` >>

  `symb_matchstate sr sys H_2 s` by (
    METIS_TAC [symb_subst_sound_thm1]
  ) >>

  `?H_2_m. symb_minimal_interpretation sr sys H_2_m /\ symb_matchstate sr sys H_2_m s /\ symb_interpr_ext H_2 H_2_m` by (
    (* minimize H_2 wrt sys *)
    METIS_TAC [symb_matchstate_TO_minimal_thm]
  ) >>

  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H)` by (
    FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def, GSYM DELETE_DEF] >>
    METIS_TAC [SUBSET_REFL, UNION_SUBSET, SUBSET_DELETE_BOTH, DELETE_DELETE]
  ) >>
  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H_2_m)` by (
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
    METIS_TAC [DELETE_SUBSET, SUBSET_TRANS]
  ) >>
  `symb_interprs_eq_for H H_2_m (symb_symbols sr sys DELETE symb)` by (
    `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def, GSYM DELETE_DEF] >>
      METIS_TAC [SUBSET_REFL, UNION_SUBSET, SUBSET_DELETE_BOTH, DELETE_DELETE]
    ) >>
    `symb_interprs_eq_for H H_2 (symb_symbols sr sys DELETE symb)` by (
      METIS_TAC [symb_interprs_eq_for_UPDATE_dom_thm, symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm]
    ) >>
    `symb_interprs_eq_for H_2 H_2_m (symb_symbols sr sys DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def] >>
      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>

  (* now execute without substitution *)
  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys_A H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H_2_m`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss) [] >>

  (* now have to go from sys' in Pi to Pi_s ... that is, all that follows *)
  Q.ABBREV_TAC `sys_s' = symb_subst sr (symb,symb_inst) sys'` >>
  `sys_s' IN Pi_s` by (
    METIS_TAC [symb_subst_set_def, IN_IMAGE]
  ) >>

  Q.EXISTS_TAC `sys_s'` >>
  ASM_SIMP_TAC (std_ss) [] >>

  (* now have to establish an interpretation that can match and is an extension of the initial H *)

  (* we may miss some symbols in H' now (or have some additional symbols) *)
  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H')` by (
    METIS_TAC [symb_interpr_ext_IMP_dom_thm, SUBSET_TRANS]
  ) >>
  `symb_interprs_eq_for H H' (symb_symbols sr sys DELETE symb)` by (
    `symb_interprs_eq_for H_2_m H' (symb_symbols sr sys DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def] >>
      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>

  `?H_3_m. symb_minimal_interpretation sr sys' H_3_m /\ symb_matchstate sr sys' H_3_m s' /\ symb_interpr_ext H' H_3_m` by (
    (* minimize H' wrt sys' *)
    METIS_TAC [symb_matchstate_TO_minimal_thm]
  ) >>
  (* ... *)

  Q.ABBREV_TAC `H_4v = symb_interpr_update H_3_m (symb,SOME v)` >>
  `symb_matchstate sr sys' H_4v s'` by (
    Cases_on `~(symb IN symb_symbols sr sys')` >- (
      METIS_TAC [symb_matchstate_UPDATE_indep_thm]
    ) >>

    `symb_interpr_get H_2 symb = symb_interpr_get H_3_m symb` by (
      `symb_interpr_get H_2 symb = SOME v` by (
        METIS_TAC [symb_interpr_get_update_thm]
      ) >>
      `symb_interpr_get H_2 symb = symb_interpr_get H_2_m symb` by (
        METIS_TAC [
          symb_matchstate_def,
          symb_suitable_interpretation_def,
          symb_interpr_for_symbs_def,
          symb_interpr_ext_IMP_eq_for_SING_thm,
          SUBSET_DEF
        ]
      ) >>
      `symb_interpr_get H_2_m symb = symb_interpr_get H' symb` by (
        METIS_TAC [symb_interpr_ext_IMP_eq_for_SING_thm2]
      ) >>
      `symb_interpr_get H' symb = symb_interpr_get H_3_m symb` by (
        METIS_TAC [
          symb_matchstate_def,
          symb_suitable_interpretation_def,
          symb_interpr_for_symbs_def,
          symb_interpr_ext_IMP_eq_for_SING_thm,
          SUBSET_DEF
        ]
      ) >>
      ASM_REWRITE_TAC []
    ) >>

    `H_4v = H_3_m` by (
      SIMP_TAC std_ss [symb_interpr_EQ_thm] >>
      GEN_TAC >>
      Cases_on `symb' = symb` >> (
        METIS_TAC [symb_interpr_get_update_thm]
      )
    ) >>

    METIS_TAC []
  ) >>

  Q.ABBREV_TAC `H_4 = symb_interpr_extend H_2_m H_4v` >>
  `symb_matchstate sr sys' H_4 s'` by (
    METIS_TAC [symb_interpr_extend_IMP_symb_matchstate_thm, symb_matchstate_def]
  ) >>

  Q.ABBREV_TAC `H_4w = symb_interpr_extend H_2_m H_3_m` >>
  `symb_interprs_eq_for H H_4w (symb_symbols sr sys DELETE symb)` by (
    `symb_interpr_ext H_4w H_2_m` by (
      METIS_TAC
        [symb_interpr_ext_IMP_interprs_eq_for_INTER_thm,
         symb_interpr_extend_IMP_ext_thm2]
    ) >>
    `symb_interprs_eq_for H' H_4w (symb_symbols sr sys DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def] >>
      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm, symb_interprs_eq_for_TRANS_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>
  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H_4w)` by (
    METIS_TAC [symb_interprs_eq_for_IMP_dom_thm]
  ) >>
  `H_4 = symb_interpr_update H_4w (symb,SOME v)` by (
    SIMP_TAC std_ss [symb_interpr_EQ_thm] >>
    GEN_TAC >>
    Q.UNABBREV_TAC `H_4` >>
    Q.UNABBREV_TAC `H_4w` >>
    Q.UNABBREV_TAC `H_4v` >>
    SIMP_TAC std_ss [symb_interpr_get_def, symb_interpr_extend_def, symb_interpr_update_def, symb_interpr_dom_UPDATE_SOME_thm, symb_interpr_get_update_thm] >>
    Cases_on `symb' = symb` >> (
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    )
  ) >>
  `symb_interprs_eq_for H H_4 (symb_symbols sr sys DELETE symb)` by (
    `symb_interprs_eq_for H_4w H_4 (symb_symbols sr sys DELETE symb)` by (
      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_update_thm, symb_interprs_eq_for_ID_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>
  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H_4)` by (
    METIS_TAC [symb_interprs_eq_for_IMP_dom_thm]
  ) >>
  (* ... *)

  Q.ABBREV_TAC `H_5 = symb_interpr_extend H H_4` >>
  `symb_matchstate sr sys' H_5 s'` by (
    METIS_TAC [symb_interpr_extend_IMP_symb_matchstate_thm, symb_matchstate_def]
  ) >>
  `symb_interprs_eq_for H H_5 (symb_symbols sr sys DELETE symb)` by (
    `symb_interpr_ext H_5 H_4` by (
      METIS_TAC [symb_interpr_extend_IMP_ext_thm]
    ) >>
    `symb_interprs_eq_for H_4 H_5 (symb_symbols sr sys DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def] >>
      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>
  `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H_5)` by (
    METIS_TAC [symb_interprs_eq_for_IMP_dom_thm]
  ) >>
  (* ... *)

  Q.ABBREV_TAC `H_6 = symb_interpr_update H_5 (symb,symb_interpr_get H symb)` >>
  `symb_interprs_eq_for H H_6 (symb_symbols sr sys DELETE symb)` by (
    `(symb_symbols sr sys DELETE symb) SUBSET (symb_interpr_dom H_5 DELETE symb)` by (
      FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def, GSYM DELETE_DEF] >>
      METIS_TAC [SUBSET_REFL, UNION_SUBSET, SUBSET_DELETE_BOTH, DELETE_DELETE]
    ) >>
    `symb_interprs_eq_for H_5 H_6 (symb_symbols sr sys DELETE symb)` by (
      METIS_TAC [symb_interprs_eq_for_UPDATE_dom_thm, symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_SUBSET_thm]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>

  `symb_interprs_eq_for H H_6 (sr.sr_symbols_f symb_inst DELETE symb)` by (
    `symb_interprs_eq_for H H_2 (sr.sr_symbols_f symb_inst DELETE symb)` by (
      METIS_TAC [symb_interprs_eq_for_update_thm, symb_interprs_eq_for_ID_thm]
    ) >>
    `symb_interprs_eq_for H_2 H_2_m ((sr.sr_symbols_f symb_inst DELETE symb) INTER symb_symbols sr sys)` by (
      `symb_interprs_eq_for H_2 H_2_m (symb_symbols sr sys)` by (
        METIS_TAC [
          symb_interpr_ext_IMP_eq_for_thm, SUBSET_REFL,
          symb_interprs_eq_for_COMM_thm,
          symb_minimal_interpretation_def,
          symb_interpr_for_symbs_min_def]
      ) >>

      METIS_TAC [symb_interprs_eq_for_INTER_symbs_thm2, INTER_COMM]
    ) >>

    `symb_interprs_eq_for H_2_m H_4 ((sr.sr_symbols_f symb_inst DELETE symb) INTER symb_symbols sr sys)` by (
      `symb_interprs_eq_for H_4w H_2_m (symb_interpr_dom H_2_m)` by (
        METIS_TAC [
          symb_interpr_ext_IMP_interprs_eq_for_INTER_thm,
          symb_interpr_extend_IMP_ext_thm2, symb_interpr_ext_def]
      ) >>
      `(symb_interpr_dom H_2_m) = (symb_symbols sr sys)` by (
        METIS_TAC [
          symb_minimal_interpretation_def,
          symb_interpr_for_symbs_min_def]
      ) >>
      `symb_interprs_eq_for H_2_m H_4w ((sr.sr_symbols_f symb_inst DELETE symb) INTER symb_symbols sr sys)` by (
        METIS_TAC [INTER_COMM, symb_interprs_eq_for_INTER_symbs_thm2, symb_interprs_eq_for_COMM_thm]
      ) >>

      `symb_interprs_eq_for H_4 H_4w
          ((sr.sr_symbols_f symb_inst DELETE symb) ∩ symb_symbols sr sys)` by (
        METIS_TAC [symb_interprs_eq_for_update_thm, symb_interprs_eq_for_ID_thm, DELETE_INTER, DELETE_DELETE]
      ) >>
      METIS_TAC [symb_interprs_eq_for_TRANS_thm, symb_interprs_eq_for_COMM_thm]
    ) >>

    `symb_interprs_eq_for H H_5 (sr.sr_symbols_f symb_inst DELETE symb)` by (
      Q.ABBREV_TAC `symbs = sr.sr_symbols_f symb_inst` >>
      Q.ABBREV_TAC `sys1mbs = symb_symbols sr sys` >>
      Q.ABBREV_TAC `sys2mbs = symb_symbols sr sys'` >>

      `symb_interpr_dom H_4 = sys1mbs UNION sys2mbs UNION {symb}` by (
        ASM_REWRITE_TAC [] >>
        Q.UNABBREV_TAC `sys1mbs` >>
        Q.UNABBREV_TAC `sys2mbs` >>
        Q.UNABBREV_TAC `H_4w` >>
        REWRITE_TAC [symb_interpr_dom_UPDATE_SOME_thm, symb_interpr_dom_extend_thm, Once INSERT_SING_UNION] >>
        METIS_TAC [UNION_ASSOC, UNION_COMM, symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def]
      ) >>
      `(symbs DELETE symb) INTER (sys2mbs DIFF sys1mbs) = EMPTY` by (
        METIS_TAC [symb_symbols_set_INTER_EMPTY_INST_thm]
      ) >>

      METIS_TAC [
        symb_interprs_eq_for_INST_thm,
        symb_interprs_eq_for_TRANS_thm
      ]
    ) >>

    `symb_interprs_eq_for H_5 H_6 (sr.sr_symbols_f symb_inst DELETE symb)` by (
      METIS_TAC [symb_interprs_eq_for_update_thm, symb_interprs_eq_for_ID_thm, DELETE_INTER, DELETE_DELETE]
    ) >>
    METIS_TAC [symb_interprs_eq_for_TRANS_thm]
  ) >>
  (* ... *)

  `symb_interpr_get H_5 symb = SOME v` by (
    `symb_interpr_get H_4v symb = SOME v` by (
      METIS_TAC [symb_interpr_get_update_thm]
    ) >>
    METIS_TAC [symb_interpr_get_extend_thm]
  ) >>

  `symb_interprs_eq_for H H_6 (sr.sr_symbols_f symb_inst)` by (
    SIMP_TAC std_ss [symb_interprs_eq_for_def] >>
    GEN_TAC >>
    Cases_on `symb' = symb` >- (
      METIS_TAC [symb_interpr_get_update_thm]
    ) >>

    REPEAT STRIP_TAC >>
    `symb' IN sr.sr_symbols_f symb_inst DELETE symb` by (
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ) >>
    METIS_TAC [symb_interprs_eq_for_def]
  ) >>
  `sr.sr_interpret_f H symb_inst = sr.sr_interpret_f H_6 symb_inst` by (
    METIS_TAC [symb_symbols_f_sound_def]
  ) >>
  `sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H_6` by (
    METIS_TAC [symb_interprs_eq_for_IMP_dom_thm]
  ) >>

  `symb_interpr_ext H_6 H` by (
    `symb_interpr_dom H = symb_symbols sr sys_s` by (
      FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def]
    ) >>
    FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_UNION_thm, GSYM DELETE_DEF] >>
    METIS_TAC [symb_interprs_eq_for_COMM_thm]
  ) >>

  `H_5 = symb_interpr_update H_6 (symb, SOME v)` by (
    SIMP_TAC std_ss [symb_interpr_EQ_thm, symb_interpr_get_update_thm] >>
    GEN_TAC >>
    Cases_on `symb' = symb` >> (
      ASM_SIMP_TAC std_ss []
    ) >>
    Q.UNABBREV_TAC `H_6` >>
    SIMP_TAC std_ss [symb_interpr_get_update_thm] >>
    ASM_SIMP_TAC std_ss []
  ) >>
  `symb_interpr_welltyped sr H_6` by (
    `symb_interpr_welltyped sr H_5` by (
      METIS_TAC [symb_matchstate_def]
    ) >>

    Cases_on `symb_interpr_get H symb` >- (
      METIS_TAC [symb_interpr_update_NONE_IMP_welltyped_thm]
    ) >>

    `sr.sr_typeof_symb symb = sr.sr_typeof_val x` by (
      METIS_TAC [symb_matchstate_def, symb_interpr_welltyped_def, symb_interpr_dom_thm, optionTheory.option_CLAUSES]
    ) >>
    METIS_TAC [symb_interpr_update_SOME_IMP_welltyped_thm]
  ) >>
  `symb_matchstate sr sys_s' H_6 s'` by (
    ASSUME_TAC ((Q.SPECL [`sr`, `H_6`, `H_5`, `symb`, `symb_inst`, `sys'`, `sys_s'`, `s'`, `v`]) symb_subst_sound_thm2) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    Cases_on `symb_interpr_get H_6 symb` >> (
      FULL_SIMP_TAC std_ss []
    ) >>

    `sr.sr_typeof_symb symb = sr.sr_typeof_val x` by (
      METIS_TAC [symb_interpr_welltyped_def, symb_interpr_dom_thm, optionTheory.option_CLAUSES]
    ) >>
    FULL_SIMP_TAC std_ss []
  ) >>

  Q.EXISTS_TAC `H_6` >>
  ASM_REWRITE_TAC []
);


(* ************************* *)
(*        RULE SPLIT         *)
(* ************************* *)
val symb_weak_bool_def = Define `
    symb_weak_bool sr symbexp =
    (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs (sr.sr_symbols_f symbexp) H) ==>

       (sr.sr_interpret_f H symbexp = SOME sr.sr_val_true
        \/
        sr.sr_interpret_f H (sr.sr_mk_exp_neg_f symbexp) = SOME sr.sr_val_true)
    )
`;

val symb_split_TRANSF_matchstate_ext_thm = store_thm(
   "symb_split_TRANSF_matchstate_ext_thm", ``
!sr.
(symb_mk_exp_conj_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_neg_f_sound sr) ==>

!sys L Pi sys2 symbexp sys2t sys2f.
  (symb_weak_bool sr symbexp) ==>

  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f symbexp)
     (sys2)
   = sys2t
  ) ==>
  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f (sr.sr_mk_exp_neg_f symbexp))
     (sys2)
   = sys2f
  ) ==>

!H s s'.
  (symb_minimal_interpretation sr sys H) ==>
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  ((symb_matchstate_ext sr sys2t H s') \/ (symb_matchstate_ext sr sys2f H s'))
``,
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``symb_matchstate_ext A B C D`` (ASSUME_TAC o REWRITE_RULE [symb_matchstate_ext_def]) >>
  FULL_SIMP_TAC std_ss [] >>

  Q.ABBREV_TAC `H2 = symb_interpr_extend_symbs_sr sr (sr.sr_symbols_f symbexp) H'` >>
  `symb_interpr_welltyped sr H2` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_welltyped_thm, symb_matchstate_def]
  ) >>
  `symb_interpr_ext H2 H'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IS_interpr_ext_thm]
  ) >>
  `symb_interpr_ext H2 H` by (
    METIS_TAC [symb_interpr_ext_TRANS_thm]
  ) >>
  `symb_matchstate sr sys2 H2 s'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_matchstate_thm]
  ) >>
  `symb_interpr_for_symbs (sr.sr_symbols_f symbexp) H2` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IS_interpr_for_symbs_thm]
  ) >>

  IMP_RES_TAC symb_weak_bool_def >| [
    DISJ1_TAC >>
    FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>
    Q.EXISTS_TAC `H2` >>
    FULL_SIMP_TAC std_ss [] >>

    `symb_interpr_symbpcond sr H2 sys2t` by (
      PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (K ALL_TAC) >>
      PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (ASSUME_TAC o GSYM) >>

      FULL_SIMP_TAC std_ss [] >>
      Cases_on `sys2` >>
      FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_interpr_symbpcond_def, symb_symbst_pcond_def] >>

      `sr.sr_interpret_f H2 c = SOME sr.sr_val_true` by (
        METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def, symb_symbst_pcond_def]
      ) >>

      METIS_TAC [symb_mk_exp_conj_f_sound_def]
    ) >>

    `symb_suitable_interpretation sr sys2t H2` by (
      `symb_symbols sr sys2t SUBSET symb_symbols sr sys2 UNION sr.sr_symbols_f symbexp` by (
        `symb_symbols sr sys2t SUBSET symb_symbols sr sys2 UNION (sr.sr_symbols_f symbexp UNION sr.sr_symbols_f (symb_symbst_pcond sys2))` by (
          METIS_TAC [symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm, symb_mk_exp_conj_f_sound_def]
        ) >>

        METIS_TAC [symb_symbols_SUBSET_pcond_thm,
         SUBSET_UNION_ABSORPTION,
         UNION_COMM,
         UNION_ASSOC]
      ) >>

      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_SUBSET_dom_thm] >>

      METIS_TAC [symb_interpr_for_symbs_def,
        matchstate_IMP_symbols_SUBSET_interpr_dom_thm,
        UNION_SUBSET, SUBSET_TRANS]
    ) >>

    PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (K ALL_TAC) >>
    PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (ASSUME_TAC o GSYM) >>
    Cases_on `sys2` >> Cases_on `sys2t` >>
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_symbst_pcond_update_READ_thm, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_pcond_def, symb_symbst_extra_def, symb_symbst_pcond_update_def, symb_symbst_t_11] >>
    METIS_TAC []
  ,
    DISJ2_TAC >>
    FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>
    Q.EXISTS_TAC `H2` >>
    FULL_SIMP_TAC std_ss [] >>

    `symb_interpr_symbpcond sr H2 sys2f` by (
      PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (ASSUME_TAC o GSYM) >>

      FULL_SIMP_TAC std_ss [] >>
      Cases_on `sys2` >>
      FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_interpr_symbpcond_def, symb_symbst_pcond_def] >>

      `sr.sr_interpret_f H2 c = SOME sr.sr_val_true` by (
        METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def, symb_symbst_pcond_def]
      ) >>

      METIS_TAC [symb_mk_exp_conj_f_sound_def]
    ) >>

    `symb_suitable_interpretation sr sys2f H2` by (
      `symb_symbols sr sys2f SUBSET symb_symbols sr sys2 UNION sr.sr_symbols_f symbexp` by (
        `symb_symbols sr sys2f SUBSET symb_symbols sr sys2 UNION (sr.sr_symbols_f symbexp UNION sr.sr_symbols_f (symb_symbst_pcond sys2))` by (
          METIS_TAC [symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm, symb_mk_exp_conj_f_sound_def, symb_mk_exp_neg_f_sound_def]
        ) >>

        METIS_TAC [symb_symbols_SUBSET_pcond_thm,
         SUBSET_UNION_ABSORPTION,
         UNION_COMM,
         UNION_ASSOC]
      ) >>

      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_SUBSET_dom_thm] >>

      METIS_TAC [symb_interpr_for_symbs_def,
        matchstate_IMP_symbols_SUBSET_interpr_dom_thm,
        UNION_SUBSET, SUBSET_TRANS]
    ) >>

    PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (ASSUME_TAC o GSYM) >>
    Cases_on `sys2` >> Cases_on `sys2f` >>
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_symbst_pcond_update_READ_thm, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_pcond_def, symb_symbst_extra_def, symb_symbst_pcond_update_def, symb_symbst_t_11] >>
    METIS_TAC []
  ]
);

val symb_rule_SPLIT_thm = store_thm(
   "symb_rule_SPLIT_thm", ``
!sr.
(symb_mk_exp_conj_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_neg_f_sound sr) ==>

!sys L Pi sys2 symbexp sys2t sys2f.
  (symb_weak_bool sr symbexp) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>

  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f symbexp)
     (sys2)
   = sys2t
  ) ==>
  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f (sr.sr_mk_exp_neg_f symbexp))
     (sys2)
   = sys2f
  ) ==>

  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2t; sys2f}))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC symb_split_TRANSF_matchstate_ext_thm >>

  `(!H s s'.
     (symb_minimal_interpretation sr sys H) ==>
     (symb_matchstate sr sys H s) ==>
(*
     (symb_interpr_ext H' H) ==>
     (symb_matchstate sr sys2 H' s') ==>
*)
     (symb_matchstate_ext sr sys2 H s') ==>
     (?sys2'. (sys2' IN {sys2t; sys2f}) /\ symb_matchstate_ext sr sys2' H s')
  )` by (
    POP_ASSUM (fn t => REPEAT (POP_ASSUM (K ALL_TAC)) >> ASSUME_TAC t) >>
    FULL_SIMP_TAC std_ss [pred_setTheory.EXISTS_IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
    METIS_TAC []
  ) >>

  METIS_TAC [symb_rule_TRANSF_GEN2_thm]
);


(* ************************* *)
(*        RULE SRENAME       *)
(* ************************* *)
val symb_rule_SRENAME_thm = store_thm(
   "symb_rule_SRENAME_thm", ``
!sr.
!sys L Pi symb symb_new.
  (* TODO: maybe need more or less of these assumptions *)
  (symb_typeof_exp_sound sr) ==>
  (symb_subst_f_sound sr) ==>
  (symb_subst_f_sound_NOTIN sr) ==>
  (symb_symbols_f_sound sr) ==>
  (symb_mk_exp_symb_f_sound sr) ==>
  (symb_mk_exp_symb_f_sound_typeof sr) ==>

  (sr.sr_typeof_symb symb_new = sr.sr_typeof_symb symb) ==>

  (* exclude the new symbol from all symbols that are in use *)
  (symb_new NOTIN ((symb_symbols sr sys) UNION (symb_symbols_set sr Pi))) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (symb_subst sr (symb, sr.sr_mk_exp_symb_f symb_new) sys, L, symb_subst_set sr (symb, sr.sr_mk_exp_symb_f symb_new) Pi))
``,
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `symb_inst = sr.sr_mk_exp_symb_f symb_new` >>
  `(sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb))` by (
    METIS_TAC [symb_mk_exp_symb_f_sound_typeof_def]
  ) >>
  `(sr.sr_symbols_f symb_inst = {symb_new})` by (
    METIS_TAC [symb_mk_exp_symb_f_sound_def]
  ) >>

  Cases_on `symb IN symb_symbols sr sys` >- (
    `sr.sr_symbols_f symb_inst INTER (symb_symbols_set sr Pi DIFF symb_symbols sr sys) = EMPTY` by (
      `{symb_new} INTER symb_symbols_set sr Pi = EMPTY` by (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [INSERT_INTER]
      ) >>

      METIS_TAC [INTER_COMM, DIFF_INTER, EMPTY_DIFF]
    ) >>
    METIS_TAC [symb_rule_INST_thm]
  ) >>

(* do we have theorem that substition has no effect if substituted symbol is not present? then this part of the proof will be relatively simple and just needs a bit argument for the last step *)
  FULL_SIMP_TAC std_ss [symb_hl_step_in_L_sound_def, conc_step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  `symb_subst sr (symb,symb_inst) sys = sys` by (
    METIS_TAC [symb_subst_sound_NOTIN_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (IMP_RES_TAC) >>
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss) [] >>

  Q.ABBREV_TAC `sys_s = symb_subst sr (symb,symb_inst) sys'` >>
  Q.ABBREV_TAC `Pi_s = symb_subst_set sr (symb,symb_inst) Pi` >>
  Q.EXISTS_TAC `sys_s` >>
  `sys_s IN Pi_s` by (
    METIS_TAC [symb_subst_set_def, IN_IMAGE]
  ) >>
  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  Cases_on `symb NOTIN symb_symbols sr sys'` >- (
    `symb_subst sr (symb,symb_inst) sys' = sys'` by (
      METIS_TAC [symb_subst_sound_NOTIN_thm]
    ) >>
    METIS_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `symb_new NOTIN symb_symbols sr sys /\ symb_new NOTIN symb_symbols sr sys'` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC [symb_symbols_set_SUBSET_thm, SUBSET_THM]
  ) >>

  `?H2.
     symb_interpr_ext H2 H /\
     symb_matchstate sr sys' H2 s' /\
     symb_new NOTIN symb_interpr_dom H2
  ` by (
    Q.ABBREV_TAC `H2 = symb_interpr_update H' (symb_new, NONE)` >>
    Q.EXISTS_TAC `H2` >>
    `symb_interprs_eq_for H2 H' (symb_interpr_dom H' DELETE symb_new)` by (
      METIS_TAC [symb_interprs_eq_for_UPDATE_dom_thm]
    ) >>

    `symb_interpr_ext H2 H` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def] >>
      `symb_symbols sr sys = symb_interpr_dom H` by (
        METIS_TAC [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def]
      ) >>
      FULL_SIMP_TAC std_ss [] >>

      `symb_interprs_eq_for H2 H' (symb_interpr_dom H)` by (
        `symb_interpr_dom H SUBSET symb_interpr_dom H' DELETE symb_new` by (
          FULL_SIMP_TAC std_ss [GSYM symb_interpr_ext_def] >>
          METIS_TAC [symb_interpr_ext_IMP_dom_thm, SUBSET_DELETE]
        ) >>
        METIS_TAC [symb_interprs_eq_for_SUBSET_thm]
      ) >>

      METIS_TAC [symb_interprs_eq_for_COMM_thm, symb_interprs_eq_for_TRANS_thm]
    ) >>

    `symb_matchstate sr sys' H2 s'` by (
      `symb_interprs_eq_for H2 H' (symb_symbols sr sys')` by (
        `symb_symbols sr sys' SUBSET symb_interpr_dom H'` by (
          METIS_TAC [matchstate_IMP_symbols_SUBSET_interpr_dom_thm]
        ) >>

        METIS_TAC [symb_interprs_eq_for_SUBSET_thm, SUBSET_DELETE]
      ) >>

      `symb_interpr_welltyped sr H2` by (
        METIS_TAC [symb_interpr_update_NONE_IMP_welltyped_thm, symb_matchstate_def]
      ) >>

      METIS_TAC [symb_interprs_eq_for_matchstate_IMP_matchstate_thm, symb_matchstate_def]
    ) >>

    ASM_REWRITE_TAC [symb_interpr_dom_thm] >>
    METIS_TAC [symb_interpr_get_update_id_thm]
  ) >>

  `?v. symb_interpr_get H2 symb = SOME v /\ sr.sr_typeof_val v = sr.sr_typeof_symb symb` by (
    `symb_interpr_welltyped sr H2` by (
      METIS_TAC [symb_matchstate_def]
    ) >>

    (* we know that symb is mapped in H2 (via the symbol set of sys') *)
    `symb IN symb_interpr_dom H2` by (
      METIS_TAC [matchstate_IMP_symbols_SUBSET_interpr_dom_thm, SUBSET_THM]
    ) >>

    METIS_TAC [symb_interpr_welltyped_def]
  ) >>

  Q.ABBREV_TAC `H3 = symb_interpr_update H2 (symb_new,SOME v)` >>

  (* also allows (together with equalities in the assumptions) to satisfy welltypedness requirement of symb_subst_sound_thm2 later *)
  `symb_interpr_get H3 symb = SOME v` by (
    Cases_on `symb = symb_new` >- (
      FULL_SIMP_TAC std_ss []
    ) >>

    Q.UNABBREV_TAC `H3` >>
    FULL_SIMP_TAC std_ss [symb_interpr_get_update_thm]
  ) >>

(*
  Q.ABBREV_TAC `H4 = symb_interpr_update H3 (symb,SOME v)` >>
*)
  `symb_interpr_update H3 (symb,SOME v) = H3` by (
    Q.UNABBREV_TAC `H3` >>
    Q.ABBREV_TAC `abc = symb_interpr_update H2 (symb_new,SOME v)` >>
    REWRITE_TAC [symb_interpr_EQ_thm] >>
    REPEAT STRIP_TAC >>

    Cases_on `symb = symb'` >> (
      FULL_SIMP_TAC std_ss [symb_interpr_get_update_thm]
    )
  ) >>

  `symb_interpr_ext H3 H` by (
    Q.UNABBREV_TAC `H3` >>
    METIS_TAC [symb_interpr_ext_TRANS_thm, symb_interpr_ext_UPDATE_thm]
  ) >>

  `symb_matchstate sr sys' H3 s'` by (
    `symb_interprs_eq_for H2 H3 (symb_symbols sr sys')` by (
      FULL_SIMP_TAC std_ss [symb_interprs_eq_for_def] >>
      REPEAT STRIP_TAC >>
      Q.UNABBREV_TAC `H3` >>

      Cases_on `symb_new = symb'` >> (
        FULL_SIMP_TAC std_ss [symb_interpr_get_update_thm]
      )
    ) >>

    `symb_interpr_welltyped sr H3` by (
      METIS_TAC [symb_interpr_update_SOME_IMP_welltyped_thm, symb_matchstate_def]
    ) >>

    METIS_TAC [symb_interprs_eq_for_matchstate_IMP_matchstate_thm, symb_matchstate_def]
  ) >>

  `symb_matchstate sr sys_s H3 s'` by (
    `sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H3` by (
      Q.UNABBREV_TAC `H3` >>
      Q.UNABBREV_TAC `symb_inst` >>
      FULL_SIMP_TAC std_ss [symb_mk_exp_symb_f_sound_def, symb_interpr_dom_UPDATE_SOME_thm] >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ) >>
    `sr.sr_interpret_f H3 symb_inst = SOME v` by (
      `symb_interpr_get H3 symb_new = SOME v` by (
        METIS_TAC [symb_interpr_get_update_id_thm]
      ) >>
      METIS_TAC [symb_mk_exp_symb_f_sound_def]
    ) >>
    `!v'.
          symb_interpr_get H3 symb = SOME v' ==>
          sr.sr_typeof_symb symb = sr.sr_typeof_val v'` by (
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss []
    ) >>
    METIS_TAC [symb_subst_sound_thm2]
  ) >>

  METIS_TAC []
);


(* ************************* *)
(*        STRENGTHEN         *)
(* ************************* *)
val symb_strengthen_TRANSF_matchstate_ext_thm = store_thm(
   "symb_strengthen_TRANSF_matchstate_ext_thm", ``
!sr.
(symb_mk_exp_conj_f_sound sr) ==>
(symb_symbols_f_sound sr) ==>

!sys1 L Pi sys2 pcond sys2'.
  (symb_pcondwiden sr (symb_symbst_pcond sys1) pcond) ==>
  ((sr.sr_symbols_f pcond) SUBSET (sr.sr_symbols_f (symb_symbst_pcond sys1))) ==> (* this assumption simplifies the proof but is not really needed *)
  (* ALTERNATIVE: sys1 /\ sys2 ==> sys2' *)

  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f pcond)
     (sys2)
   = sys2'
  ) ==>

!H s s'.
  (symb_minimal_interpretation sr sys1 H) ==>
  (symb_matchstate sr sys1 H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  (symb_matchstate_ext sr sys2' H s')
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>
  Q.EXISTS_TAC `H'` >>
  FULL_SIMP_TAC std_ss [] >>

(*
symb_matchstate_def
symb_pcondwiden_def
*)

  (* TODO: not true if we remove the assumption on the symbols of pcond, then need to play with H' first *)
  `symb_interpr_symbpcond sr H' sys2'` by (
    `symb_interpr_welltyped sr H'` by (
      METIS_TAC [symb_matchstate_def]
    ) >>

    `symb_interpr_symbpcond sr H' sys2` by (
      METIS_TAC [symb_matchstate_def]
    ) >>

    FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def] >>

    `sr.sr_mk_exp_conj_f pcond (symb_symbst_pcond sys2) = (symb_symbst_pcond sys2')` by (
      METIS_TAC [symb_symbst_pcond_update_READ_thm]
    ) >>

    `sr.sr_interpret_f H' pcond = SOME sr.sr_val_true` by (
      `symb_interpr_for_symbs
             (sr.sr_symbols_f (symb_symbst_pcond sys1) UNION sr.sr_symbols_f pcond) H'` by (
        METIS_TAC [symb_interpr_for_symbs_def, symb_interpr_ext_IMP_dom_thm, matchstate_IMP_symbols_SUBSET_interpr_dom_thm, symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS, UNION_SUBSET]
      ) >>

      `sr.sr_interpret_f H' (symb_symbst_pcond sys1) = SOME sr.sr_val_true` by (
        `sr.sr_interpret_f H (symb_symbst_pcond sys1) = SOME sr.sr_val_true` by (
          METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def]
        ) >>
        `symb_interprs_eq_for H H' (sr.sr_symbols_f (symb_symbst_pcond sys1))` by (
          METIS_TAC [symb_symbols_SUBSET_pcond_thm,
                     SUBSET_TRANS, symb_interpr_ext_IMP_eq_for_thm,
                     matchstate_IMP_symbols_SUBSET_interpr_dom_thm]
        ) >>
        METIS_TAC [symb_symbols_f_sound_def]
      ) >>

      METIS_TAC [symb_pcondwiden_def]
    ) >>

    METIS_TAC [symb_mk_exp_conj_f_sound_def]
  ) >>

(*
symb_symbst_pcond_update_IMP_matchstate_EQ_thm
*)

  `symb_symbols sr sys2 UNION sr.sr_symbols_f ((sr.sr_mk_exp_conj_f pcond) (symb_symbst_pcond sys2)) SUBSET symb_interpr_dom H'` by (
    FULL_SIMP_TAC std_ss [symb_mk_exp_conj_f_sound_def] >>

    `symb_symbols sr sys2 SUBSET symb_interpr_dom H'` by (
      METIS_TAC [matchstate_IMP_symbols_SUBSET_interpr_dom_thm]
    ) >>

    `sr.sr_symbols_f (symb_symbst_pcond sys2) SUBSET symb_interpr_dom H'` by (
      METIS_TAC [symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS]
    ) >>

    `sr.sr_symbols_f pcond SUBSET symb_interpr_dom H'` by (
      METIS_TAC [symb_interpr_ext_IMP_dom_thm, matchstate_IMP_symbols_SUBSET_interpr_dom_thm, symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS]
    ) >>

    METIS_TAC [UNION_SUBSET]
  ) >>

  PAT_X_ASSUM ``symb_symbst_pcond_update A B = C`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_symbst_pcond_update_UNCHANGED_thm, symb_symbst_pcond_update_READ_thm] >>

  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>

  METIS_TAC [symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm, SUBSET_TRANS]
);

val symb_rule_STRENGTHEN_thm = store_thm(
   "symb_rule_STRENGTHEN_thm", ``
!sr.
!sys1 L Pi pcond sys2 sys2'.

  (* TODO: maybe need more or less of these assumptions *)
  (symb_symbols_f_sound sr) ==>
  (symb_mk_exp_conj_f_sound sr) ==>


  (symb_pcondwiden sr (symb_symbst_pcond sys1) pcond) ==>
  ((sr.sr_symbols_f pcond) SUBSET (sr.sr_symbols_f (symb_symbst_pcond sys1))) ==> (* this assumption simplifies the proof but is not really needed *)
  (* ALTERNATIVE: sys1 /\ sys2 ==> sys2' *)

  (symb_symbst_pcond_update
     (sr.sr_mk_exp_conj_f pcond)
     (sys2)
   = sys2'
  ) ==>

  (symb_hl_step_in_L_sound sr (sys1, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (sys1, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_strengthen_TRANSF_matchstate_ext_thm, symb_rule_TRANSF_GEN_thm]
);

(*
  next step, adjust CONS rule:
    - S1' -> Pi, S2
    - S1 ==> S1'
    - S2 ==> S2'
    ====>>>>
    - S1 -> Pi, (S2' pcond/\ S1[']pcond)
 *)




val _ = export_theory();
