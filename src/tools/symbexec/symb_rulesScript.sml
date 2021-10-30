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

  (* we can construct an interpretation that both matches this symbolic state
     with the concrete final state and is an extension of the initial interpretation *)
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm, symb_matchstate_ext_def]
);


(* ************************* *)
(*         RULE INF          *)
(* ************************* *)
val symb_rule_INF_thm = store_thm(
   "symb_rule_INF_thm", ``
!sr.
!sys L Pi sys'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (!H. ~(symb_interpr_symbpcond sr H sys')) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi DIFF {sys'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_matchstate_ext_def] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `sys' = sys''` >> (
    METIS_TAC []
  )
);


(* ************************* *)
(*        RULE CONS          *)
(* ************************* *)
val symb_pcondwiden_def = Define `
  symb_pcondwiden sr sys sys' = (
    (symb_symbst_extra sys =
     symb_symbst_extra sys') /\
    (symb_symbst_pc sys =
     symb_symbst_pc sys') /\
    (symb_symbst_store sys =
     symb_symbst_store sys') /\
    (!H.
      (symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION (sr.sr_symbols_f (symb_symbst_pcond sys'))) H) ==>
      (symb_interpr_symbpcond sr H sys) ==>
      (symb_interpr_symbpcond sr H sys'))
  )
`;

val symb_pcondwiden_matchstate_IMP_matchstate_thm = store_thm(
   "symb_pcondwiden_matchstate_IMP_matchstate_thm", ``
!sr.
!sys sys' H s.
  (symb_symbols_f_sound sr) ==>

  (symb_pcondwiden sr sys sys') ==>
  (symb_matchstate sr sys H s) ==>

  (symb_matchstate sr sys' (symb_interpr_extend_symbs (symb_symbols sr sys') H) s)
``,
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `H' = (symb_interpr_extend_symbs (symb_symbols sr sys') H)` >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm, symb_interpr_extend_symbs_IMP_ext_thm]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm,
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

  FULL_SIMP_TAC std_ss [symb_pcondwiden_def, symb_matchstate_def] >>

  METIS_TAC [symb_symbst_store_IMP_EQ_thm]
);

val symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm = store_thm(
   "symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm", ``
!sr.
!sys1 sys2 s H1 H2.
  (symb_symbols_f_sound sr) ==>

  (symb_pcondwiden sr sys1 sys2) ==>

  (symb_matchstate sr sys1 H1 s) ==>
  (?H2.
    (symb_interpr_ext H2 H1) /\
    (symb_matchstate sr sys2 H2 s))
``,
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `symb_interpr_extend_symbs (symb_symbols sr sys2) H1` >>

  FULL_SIMP_TAC std_ss [symb_interpr_extend_symbs_IMP_ext_thm] >>

  METIS_TAC [symb_pcondwiden_matchstate_IMP_matchstate_thm]
);

(* TODO: split this into two *)
val symb_rule_CONS_S_thm = store_thm(
   "symb_rule_CONS_S_thm", ``
!sr.
!sys' sys L Pi.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr Pi) DIFF (symb_symbols sr sys')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys', L, Pi)) ==>
  (symb_pcondwiden sr sys sys') ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  rename1 `symb_minimal_interpretation sr sys H1` >>

  (* extend H to include arbitrary mappings for everything missing w.r.t. sys',
       this is like the other rule CONS_E *)
  (* Q.ABBREV_TAC `H_a = symb_interpr_extend_symbs (symb_symbols sr sys') H1` >> *)
  (* this can now match sys' with s *)
  IMP_RES_TAC symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm >>
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
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm, symb_matchstate_ext_def]
);

val symb_pcondwiden_TRANSF_matchstate_ext_thm = store_thm(
   "symb_pcondwiden_TRANSF_matchstate_ext_thm", ``
!sr.
!sys sys2 sys2'.
  (symb_symbols_f_sound sr) ==>

  (symb_pcondwiden sr sys2 sys2') ==>

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
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_pcondwiden_matchstate_IMP_matchstate_thm]
);


val symb_rule_CONS_E_thm = store_thm(
   "symb_rule_CONS_E_thm", ``
!sr.
!sys L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_pcondwiden_TRANSF_matchstate_ext_thm]
);

val symb_rule_CONS_thm = store_thm(
   "symb_rule_CONS_thm", ``
!sr.
!sys1' sys1 L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys1) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr ((Pi DIFF {sys2}) UNION {sys2'})) DIFF (symb_symbols sr sys1')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys1', L, Pi)) ==>
  (symb_pcondwiden sr sys1 sys1') ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys1, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_CONS_S_thm, symb_rule_CONS_E_thm]
);


(* ************************* *)
(*        RULE FRESH         *)
(* ************************* *)
(* construct symbolic expression with semantics of
     conjuncting an expression with an equality of two other expressions
   e.g.: e1 = (v), e2 = (5), conj1 = (x > 10)
     then: (v) = (5) /\ (x > 10) *)
val symb_mk_exp_eq_f_sound_def = Define `
    symb_mk_exp_eq_f_sound sr =
      ((!e1 e2. !H.
         (sr.sr_interpret_f H (sr.sr_mk_exp_eq_f e1 e2) = SOME sr.sr_val_true) =
         ((sr.sr_interpret_f H e1 <> NONE) /\
          (sr.sr_interpret_f H e1 =
           sr.sr_interpret_f H e2))) /\
       (!e1 e2. sr.sr_symbols_f (sr.sr_mk_exp_eq_f e1 e2) =
         sr.sr_symbols_f e1 UNION sr.sr_symbols_f e2))
`;
val symb_mk_exp_conj_f_sound_def = Define `
    symb_mk_exp_conj_f_sound sr =
      ((!e1 e2. !H.
         (sr.sr_interpret_f H (sr.sr_mk_exp_conj_f e1 e2) = SOME sr.sr_val_true) =
         ((sr.sr_interpret_f H e1 = SOME sr.sr_val_true) /\
          (sr.sr_interpret_f H e2 = SOME sr.sr_val_true))) /\
       (!e1 e2. sr.sr_symbols_f (sr.sr_mk_exp_conj_f e1 e2) =
         sr.sr_symbols_f e1 UNION sr.sr_symbols_f e2))
`;
val symb_expr_conj_eq_def = Define `
    symb_expr_conj_eq sr e1 e2 conj1 =
      sr.sr_mk_exp_conj_f (sr.sr_mk_exp_eq_f e1 e2) conj1
`;
val symb_expr_conj_eq_thm = store_thm(
   "symb_expr_conj_eq_thm", ``
!sr.
  (symb_mk_exp_eq_f_sound sr) ==>
  (symb_mk_exp_conj_f_sound sr) ==>
    ((!e1 e2 conj1. !H.
       (sr.sr_interpret_f H (symb_expr_conj_eq sr e1 e2 conj1) = SOME sr.sr_val_true) =
       ((sr.sr_interpret_f H conj1 = SOME sr.sr_val_true) /\
        (sr.sr_interpret_f H e1 <> NONE) /\
        (sr.sr_interpret_f H e1 =
         sr.sr_interpret_f H e2))) /\
     (!e1 e2 conj1.sr.sr_symbols_f (symb_expr_conj_eq sr e1 e2 conj1) =
         sr.sr_symbols_f e1 UNION
         sr.sr_symbols_f e2 UNION
         sr.sr_symbols_f conj1))
``,
  METIS_TAC [symb_expr_conj_eq_def, symb_mk_exp_eq_f_sound_def, symb_mk_exp_conj_f_sound_def]
);

(* predicate for functions that make expressions that represent exactly a symbol *)
val symb_mk_exp_symb_f_sound_def = Define `
    symb_mk_exp_symb_f_sound sr =
      ((!H symb v.
         (symb_interpr_get H symb = SOME v) ==>
         (sr.sr_interpret_f H (sr.sr_mk_exp_symb_f symb) = SOME v)) /\
       (!symb. sr.sr_symbols_f (sr.sr_mk_exp_symb_f symb) = {symb}))
`;

(* TODO: split this into two *)
val symb_FRESH_matchstate_IMP_matchstate_ext_thm = store_thm(
   "symb_FRESH_matchstate_IMP_matchstate_ext_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>

(!var symbexp symb sys sys' H s.
  (~(symb IN symb_interpr_dom H)) ==>
  (~(symb IN symb_symbols sr sys)) ==>

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symbexp)
     (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys)
   = sys'
  ) ==>

  (symb_matchstate sr sys  H  s) ==>
  (symb_matchstate_ext sr sys' H s)
)
``,
  REWRITE_TAC [symb_matchstate_ext_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H1 = symb_interpr_update H (symb, sr.sr_interpret_f H symbexp)` >>
  Q.EXISTS_TAC `H1` >>

  `symb_interpr_ext H1 H` by (
    METIS_TAC [symb_interpr_ext_UPDATE_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  `symb_matchstate sr sys H1 s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm]
  ) >>

  `?var_v. sr.sr_interpret_f H symbexp = SOME var_v` by (
    METIS_TAC [symb_matchstate_IMP_interpret_exp_SOME_thm]
  ) >>
  `sr.sr_interpret_f H1 symbexp = SOME var_v` by (
    METIS_TAC [symb_matchstate_ext_IMP_SAME_interpret_exp_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  (* now the prerequisites for the store update *)
  Q.ABBREV_TAC `symbexp' = (sr.sr_mk_exp_symb_f symb)` >>
  `sr.sr_symbols_f symbexp SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def,
       symb_symbols_SUBSET_store_exps_thm2, SUBSET_TRANS]
  ) >>
  `sr.sr_symbols_f symbexp' SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_mk_exp_symb_f_sound_def, symb_interpr_dom_UPDATE_SOME_thm,
       INSERT_SING_UNION, SUBSET_UNION]
  ) >>

  `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f (sr.sr_mk_exp_symb_f symb) SUBSET
       symb_interpr_dom H1` by (
    METIS_TAC [UNION_SUBSET]
  ) >>

  `sr.sr_interpret_f H1 symbexp = sr.sr_interpret_f H1 symbexp'` by (
    METIS_TAC
      [symb_mk_exp_symb_f_sound_def, symb_interpr_get_update_id_thm]
  ) >>

  (* now the store update *)
  Q.ABBREV_TAC `sys_i = (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys)` >>
  `symb_matchstate sr sys_i H1 s` by (
    METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm]
  ) >>

  (* now the prerequisites for the pcond update *)
  Q.ABBREV_TAC `pcond_f = (symb_expr_conj_eq sr symbexp' symbexp)` >>
  Q.ABBREV_TAC `pcond = symb_symbst_pcond sys_i` >>
  `sr.sr_symbols_f pcond SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def,
       symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS]
  ) >>

  `sr.sr_symbols_f pcond UNION sr.sr_symbols_f (pcond_f pcond) SUBSET
       symb_interpr_dom H1` by (
    METIS_TAC [UNION_SUBSET, symb_expr_conj_eq_thm]
  ) >>

  `sr.sr_interpret_f H1 pcond = sr.sr_interpret_f H1 (pcond_f pcond)` by (
    `(sr.sr_interpret_f H1 pcond = SOME sr.sr_val_true)` by (
      METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def]
    ) >>

    `sr.sr_interpret_f H1 symbexp <> NONE` by (
      FULL_SIMP_TAC std_ss [symb_expr_conj_eq_thm]
    ) >>

    METIS_TAC [symb_expr_conj_eq_thm]
  ) >>

  (* now the the final pcond update *)
  METIS_TAC [symb_symbst_pcond_update_IMP_matchstate_EQ_thm]
);

val symb_FRESH_TRANSF_matchstate_ext_thm = store_thm(
   "symb_FRESH_TRANSF_matchstate_ext_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>

(!sys sys2 sys2' var symbexp symb.
  (~(symb IN symb_symbols sr sys )) ==>
  (~(symb IN symb_symbols sr sys2)) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symbexp)
     (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys2)
   = sys2'
  ) ==>

!H s s'.
  (symb_minimal_interpretation sr sys H) ==>
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate_ext sr sys2 H s') ==>
  (symb_matchstate_ext sr sys2' H s')
)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  ASSUME_TAC (Q.SPECL [`sr`, `sys2`, `H`, `s'`, `symb`] symb_matchstate_ext_WITHOUT_thm) >>
  FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  METIS_TAC
   [symb_FRESH_matchstate_IMP_matchstate_ext_thm,
    symb_matchstate_ext_def, symb_interpr_ext_TRANS_thm,
    symb_FRESH_matchstate_IMP_matchstate_ext_thm,
    symb_matchstate_ext_def]
);

(* rule to introduce fresh symbols as values of store variables
     (as abbreviations or as first step of forgetting values) *)
val symb_rule_FRESH_thm = store_thm(
   "symb_rule_FRESH_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>

(!sys L Pi sys2 sys2' var symbexp symb.
  (~(symb IN symb_symbols sr sys )) ==>
  (~(symb IN symb_symbols sr sys2)) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symbexp)
     (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys2)
   = sys2'
  ) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
)
``,
  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_FRESH_TRANSF_matchstate_ext_thm]
);


(* ************************* *)
(*        RULE SUBST         *)
(* ************************* *)
val symb_simplification_def = Define `
  symb_simplification sr sys symbexp symbexp' =
    (* (((sr.sr_symbols_f symbexp') SUBSET (sr.sr_symbols_f symbexp)) /\ *)
    (!H.
     (symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION
                              (sr.sr_symbols_f symbexp) UNION
                              (sr.sr_symbols_f symbexp')) H) ==>

     (symb_interpr_symbpcond sr H sys) ==>
     (sr.sr_interpret_f H symbexp = sr.sr_interpret_f H symbexp')
    )
`;

val symb_simplification_matchstate_IMP_matchstate_thm = store_thm(
   "symb_simplification_matchstate_IMP_matchstate_thm", ``
!sr.
!var symbexp symbexp' sys sys' H H' s.
  (symb_symbols_f_sound sr) ==>

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_simplification sr sys symbexp symbexp') ==>
  (symb_symbst_store_update var symbexp' sys = sys') ==>

  (symb_matchstate sr sys H s) ==>

  ((symb_interpr_extend_symbs (symb_symbols sr sys') H) = H') ==>

  (symb_matchstate sr sys' H' s)
``,
  REPEAT STRIP_TAC >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm, symb_interpr_extend_symbs_IMP_ext_thm]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm,
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

  METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm, symb_simplification_def]
);

val symb_simplification_TRANSF_matchstate_ext_thm = store_thm(
   "symb_simplification_TRANSF_matchstate_ext_thm", ``
!sr.
!sys sys2 sys2' var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>

  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr sys2 symbexp symbexp') ==>
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
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_simplification_matchstate_IMP_matchstate_thm]
);

val symb_rule_SUBST_thm = store_thm(
   "symb_rule_SUBST_thm", ``
!sr.
!sys L Pi sys2 sys2' var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr sys2 symbexp symbexp') ==>
  (sys2' = symb_symbst_store_update var symbexp' sys2) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_TRANSF_GEN_thm, symb_simplification_TRANSF_matchstate_ext_thm]
);


(* ************************* *)
(*        RULE INST          *)
(* ************************* *)
val symb_subst_f_sound_def = Define `
    symb_subst_f_sound sr =
      (!symb symb_inst symbexp symbexp_r.
       (!H H' vo.
          (sr.sr_subst_f (symb, symb_inst) symbexp = symbexp_r) ==>
          (* NOTICE: this also captures failing interpretation, i.e. type errors *)
          (sr.sr_interpret_f H symb_inst = vo) ==>
          (* just a thought: we may want/need to require vo = SOME v, but I think it's not needed *)
          ((symb_interpr_update H (symb, vo)) = H') ==>
          (sr.sr_interpret_f H' symbexp =
           sr.sr_interpret_f H  symbexp_r)) /\
       ((sr.sr_subst_f (symb, symb_inst) symbexp = symbexp_r) ==>
        (sr.sr_symbols_f symbexp_r = ((sr.sr_symbols_f symbexp) DIFF {symb}) UNION (sr.sr_symbols_f symb_inst)))
      )
`;

(*
val symb_rule_INST_thm = store_thm(
   "symb_rule_INST_thm", ``
!sr.
  (symb_subst_f_sound sr) ==>

!sys L Pi symb symb_inst.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (substfun_st symb symb_inst sys, L, substfun_sts symb symb_inst Pi))
``,
  cheat
);
*)





val _ = export_theory();
