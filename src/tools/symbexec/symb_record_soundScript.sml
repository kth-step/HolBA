open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;

open pred_setTheory;
open combinTheory;

val _ = new_theory "symb_record_sound";


(*
ASSUMPTION: sr_symbols_f
=======================================================
*)
(* the symbols of a symbolic expression are sound if, for any symbolic expression,
   equal valuation of those in two interpretations implies the same value for the interpretation of the symbolic expression *)
val symb_symbols_f_sound_def = Define `
    symb_symbols_f_sound sr =
    (!symbexp H H'.
       (symb_interprs_eq_for H H' (sr.sr_symbols_f symbexp)) ==>
       (sr.sr_interpret_f H  symbexp =
        sr.sr_interpret_f H' symbexp))
`;

val symb_symbols_f_sound_thm = store_thm(
   "symb_symbols_f_sound_thm", ``
!sr.
    symb_symbols_f_sound sr =
    (!symbexp H H'.
       (!symb. (symb IN (sr.sr_symbols_f symbexp)) ==> (symb_interpr_get H symb = symb_interpr_get H' symb)) ==>
       (sr.sr_interpret_f H  symbexp =
        sr.sr_interpret_f H' symbexp))
``,
  REWRITE_TAC [symb_symbols_f_sound_def, symb_interprs_eq_for_def]
);

val symb_interpr_restr_interpret_EQ_thm = store_thm(
   "symb_interpr_restr_interpret_EQ_thm", ``
!sr.
!H symbs symbexp.
  (symb_symbols_f_sound sr) ==>

  ((sr.sr_symbols_f symbexp) SUBSET symbs) ==>

  (sr.sr_interpret_f H symbexp = sr.sr_interpret_f (symb_interpr_restr symbs H) symbexp)
``,
  FULL_SIMP_TAC std_ss [symb_symbols_f_sound_thm] >>
  METIS_TAC [symb_interpr_restr_thm]
);


(*
NOTATION: INTERPRETATION OF SYMBOLIC STATES AND SYMBOLIC PATH CONDITIONS
=======================================================
*)
val symb_interprs_eq_for_store_IMP_EQ_thm = store_thm(
   "symb_interprs_eq_for_store_IMP_EQ_thm", ``
!sr.
!H1 H2 store cstore.
  (symb_symbols_f_sound sr) ==>

  (symb_interprs_eq_for H1 H2 (symb_symbols_store sr store)) ==>
  ((symb_interpr_symbstore sr H1 store cstore) =
   (symb_interpr_symbstore sr H2 store cstore))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o (Q.SPEC `var`)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    METIS_TAC [symb_symbols_SUBSET_store_exps_thm,
               symb_symbols_f_sound_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS]
  )
);

val symb_interprs_eq_for_pcond_IMP_EQ_thm = store_thm(
   "symb_interprs_eq_for_pcond_IMP_EQ_thm", ``
!sr.
!H1 H2 sys.
  (symb_symbols_f_sound sr) ==>

  (symb_interprs_eq_for H1 H2 (sr.sr_symbols_f (symb_symbst_pcond sys))) ==>
  ((symb_interpr_symbpcond sr H1 sys) =
   (symb_interpr_symbpcond sr H2 sys))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def] >>
  METIS_TAC [symb_symbols_SUBSET_pcond_thm,
             symb_symbols_f_sound_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS]
);




(*
NOTATION: STATE MATCHING UNDER SOUND SYMBOL SETS
=======================================================
*)

val symb_interprs_eq_for_matchstate_IMP_matchstate_thm = store_thm(
   "symb_interprs_eq_for_matchstate_IMP_matchstate_thm", ``
!sr.
!sys H1 H2 s.
  (symb_symbols_f_sound sr) ==>

  (symb_interpr_welltyped sr H1) ==>
  (symb_interpr_welltyped sr H2) ==>

  (symb_interprs_eq_for H1 H2 (symb_symbols sr sys)) ==>
  ((symb_matchstate sr sys H1 s) =
   (symb_matchstate sr sys H2 s))
``,
  FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_SUBSET_dom_thm] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [] >>
    REPEAT STRIP_TAC >> (
      METIS_TAC ( [symb_interprs_eq_for_IMP_dom_thm, symb_interprs_eq_for_COMM_thm]
                 @[SUBSET_TRANS, symb_interprs_eq_for_SUBSET_thm]
                 @[symb_symbols_SUBSET_store_thm, symb_interprs_eq_for_store_IMP_EQ_thm]
                 @[symb_symbols_SUBSET_pcond_thm, symb_interprs_eq_for_pcond_IMP_EQ_thm])
    )
  )
);

(* matching implies matching the restricted interpretation *)
val symb_matchstate_TO_min_RESTR_thm = store_thm(
   "symb_matchstate_TO_min_RESTR_thm", ``
!sr.
!H sys s.
  (symb_symbols_f_sound sr) ==>

  (symb_matchstate sr sys H  s) ==>

  (symb_matchstate sr sys (symb_interpr_restr (symb_symbols sr sys) H) s)
``,
  METIS_TAC [symb_interpr_restr_IS_eq_for_thm, symb_interprs_eq_for_matchstate_IMP_matchstate_thm,
             symb_interpr_ext_welltyped_IMP_thm, symb_matchstate_def, symb_interpr_restr_ext_thm]
);

(* matching implies matching a minimal interpretation *)
val symb_matchstate_TO_minimal_thm = store_thm(
   "symb_matchstate_TO_minimal_thm", ``
!sr.
!sys H s.
  (symb_symbols_f_sound sr) ==>

  (symb_matchstate sr sys H s) ==>

  (?H'. (symb_interpr_ext H H')/\
        (symb_minimal_interpretation sr sys H') /\
        (symb_matchstate sr sys H' s)
  )
``,
  METIS_TAC [symb_minimal_interpretation_def, symb_matchstate_TO_min_RESTR_thm,
    symb_interpr_for_symbs_TO_min_thm, symb_matchstate_def, symb_suitable_interpretation_def]
);

val symb_interpr_ext_matchstate_IMP_matchstate_thm = store_thm(
   "symb_interpr_ext_matchstate_IMP_matchstate_thm", ``
!sr.
!sys H1 H2 s.
  (symb_symbols_f_sound sr) ==>

  (symb_interpr_ext H2 H1) ==>
  (symb_matchstate sr sys H1 s) ==>

  (symb_interpr_welltyped sr H2) ==>
  (symb_matchstate sr sys H2 s)
``,
  REPEAT STRIP_TAC >>

  `symb_interprs_eq_for H1 H2 (symb_symbols sr sys)` by (
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_SUBSET_dom_thm] >>
    METIS_TAC [symb_interpr_ext_IMP_eq_for_thm]
  ) >>

  METIS_TAC [symb_interprs_eq_for_matchstate_IMP_matchstate_thm, symb_matchstate_def]
);


val symb_interpr_extend_IMP_symb_matchstate_thm = store_thm(
   "symb_interpr_extend_IMP_symb_matchstate_thm", ``
!sr.
!sys H_extra H_base s.
  (symb_symbols_f_sound sr) ==>

  (symb_interpr_welltyped sr H_extra) ==>

  (symb_matchstate sr sys H_base s) ==>
  (symb_matchstate sr sys (symb_interpr_extend H_extra H_base) s)
``,
  METIS_TAC [symb_interpr_extend_IMP_ext_thm, symb_interpr_ext_matchstate_IMP_matchstate_thm,
             symb_matchstate_def, symb_interpr_extend_welltyped_IMP_thm]
);




val symb_matchstate_interpr_ext_EXISTS_thm = store_thm(
   "symb_matchstate_interpr_ext_EXISTS_thm", ``
!sr.
!H1 H12 H2 H23 H3 sys s.
  (symb_symbols_f_sound sr) ==>

  (symb_interpr_welltyped sr H1) ==>

  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>

  (symb_interpr_ext H12 H1) ==>
  (symb_interpr_ext H12 H2) ==>

  (symb_interpr_ext H23 H2) ==>
  (symb_interpr_ext H23 H3) ==>

  (symb_matchstate sr sys H3 s) ==>

  (symb_matchstate_ext sr sys H1 s)
(* ?H4. symb_interpr_ext H4 H1 /\ symb_matchstate sr sys H4 s) *)
``,
  REPEAT STRIP_TAC >>

  (* the intersection of H1 and H3 is equally mapped in both interpretations *)
  `symb_interprs_eq_for_INTER H1 H3` by (
    METIS_TAC [symb_interprs_eq_for_INTER_doms_thm]
  ) >>

  METIS_TAC [symb_interpr_extend_IMP_ext_thm2, symb_interpr_extend_IMP_symb_matchstate_thm,
             symb_matchstate_def, symb_interpr_extend_welltyped_IMP_thm, symb_matchstate_ext_def]
);

val symb_matchstate_ext_WITHOUT_thm = store_thm(
   "symb_matchstate_ext_WITHOUT_thm", ``
!sr.
!sys H s symb.
  (symb_symbols_f_sound sr) ==>

  (~(symb IN symb_interpr_dom H)) ==>
  (~(symb IN symb_symbols sr sys)) ==>

  (symb_matchstate_ext sr sys H s) ==>

  (?H'. (symb_interpr_ext H' H) /\
        (symb_matchstate sr sys H' s) /\
        (~(symb IN symb_interpr_dom H')))
``,
  REWRITE_TAC [symb_matchstate_ext_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H1 = symb_interpr_update H' (symb, NONE)` >>
  Q.EXISTS_TAC `H1` >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, APPLY_UPDATE_THM] >>

  `symb_interprs_eq_for H1 H' (symb_interpr_dom H)` by (
    `symb_interpr_dom H SUBSET (symb_interpr_dom H' DELETE symb)` by (
      METIS_TAC
        [symb_interpr_ext_IMP_dom_thm, SUBSET_DELETE]
    ) >>
    METIS_TAC [symb_interprs_eq_for_UPDATE_dom_thm, symb_interprs_eq_for_SUBSET_thm]
  ) >>

  `symb_interprs_eq_for H' H1 (symb_symbols sr sys)` by (
    `symb_symbols sr sys SUBSET (symb_interpr_dom H' DELETE symb)` by (
      METIS_TAC
        [symb_matchstate_def, symb_suitable_interpretation_def,
         symb_interpr_for_symbs_def, SUBSET_DELETE]
    ) >>

  METIS_TAC
    [symb_interprs_eq_for_UPDATE_dom_thm,
     symb_interprs_eq_for_SUBSET_thm, symb_interprs_eq_for_COMM_thm]
  ) >>

  `symb_interpr_welltyped sr H' /\
   symb_interpr_welltyped sr H1` by (
    METIS_TAC [symb_matchstate_def,
      symb_interpr_update_NONE_IMP_welltyped_thm]
  ) >>

  METIS_TAC
    ( [symb_interpr_ext_def, symb_interprs_eq_for_TRANS_thm]
     @[symb_interprs_eq_for_matchstate_IMP_matchstate_thm]
     @[symb_interpr_dom_UPDATE_NONE_thm, ELT_IN_DELETE])
);




(*
SOUND VALUE TYPES
=======================================================
*)
val symb_ARB_val_sound_def = Define `
    symb_ARB_val_sound sr =
      (!t. sr.sr_typeof_val (sr.sr_ARB_val t) = t)
`;

val symb_interpr_extend_symbs_sr_def = Define `
    symb_interpr_extend_symbs_sr sr =
      symb_interpr_extend_symbs (\s. sr.sr_ARB_val (sr.sr_typeof_symb s))
`;

val symb_interpr_extend_symbs_sr_IMP_welltyped_thm = store_thm(
   "symb_interpr_extend_symbs_sr_IMP_welltyped_thm", ``
!sr.
!H symbs.
  (symb_ARB_val_sound sr) ==>

  (symb_interpr_welltyped sr H) ==>
  (symb_interpr_welltyped sr (symb_interpr_extend_symbs_sr sr symbs H))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [symb_interpr_welltyped_def, symb_interpr_get_update_thm] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_def,
     symb_interpr_dom_def, symb_interpr_get_def] >>

  Cases_on `symb IN symb_interpr_dom H` >> (
    FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def, symb_ARB_val_sound_def]
  )
);

(*
SOUND EXPRESSION TYPES
=======================================================
*)
val symb_typeof_exp_sound_def = Define `
    symb_typeof_exp_sound sr =
      (!e t.
       (!H.
          (sr.sr_typeof_exp e = SOME t) ==>

          (symb_interpr_welltyped sr H) ==>
          (sr.sr_symbols_f e SUBSET symb_interpr_dom H) ==>

          (?v. (sr.sr_interpret_f H e = SOME v) /\
               (sr.sr_typeof_val v = t))
       ))
`;

val symb_interpr_update_interpret_f_IMP_welltyped_thm = store_thm(
   "symb_interpr_update_interpret_f_IMP_welltyped_thm", ``
!sr.
!H symb e.
  (symb_typeof_exp_sound sr) ==>

  (symb_interpr_welltyped sr H) ==>
  (sr.sr_symbols_f e SUBSET symb_interpr_dom H) ==>
  (sr.sr_typeof_exp e = SOME (sr.sr_typeof_symb symb)) ==>

  (symb_interpr_welltyped sr (symb_interpr_update H (symb, sr.sr_interpret_f H e)))
``,
  METIS_TAC [symb_interpr_update_SOME_IMP_welltyped_thm, symb_typeof_exp_sound_def]
);



(*
SOUND VALUE EQUALITY RELATION
=======================================================
*)
val symb_val_eq_sound_def = Define `
    symb_val_eq_sound sr =
      ((!v. sr.sr_val_eq v v)(* /\
       (!v1 v2. sr.sr_val_eq v1 v2 <=> sr.sr_val_eq v2 v1) /\
       (!v1 v2 v3. sr.sr_val_eq v1 v2 ==> sr.sr_val_eq v2 v3 ==> sr.sr_val_eq v1 v3)*)
      )
`;

(*
ASBTRACT EXPRESSION CONSTRUCTION
=======================================================
*)
(* construct symbolic expression with semantics of
     conjuncting an expression with an equality of two other expressions
   e.g.: e1 = (v), e2 = (5), conj1 = (x > 10)
     then: (v) = (5) /\ (x > 10) *)
val symb_mk_exp_eq_f_sound_def = Define `
    symb_mk_exp_eq_f_sound sr =
      ((!e1 e2 H.
         (symb_interpr_welltyped sr H) ==>
         (sr.sr_interpret_f H (sr.sr_mk_exp_eq_f e1 e2) = SOME sr.sr_val_true) =
         ((sr.sr_interpret_f H e1 <> NONE) /\
          (OPTREL sr.sr_val_eq (sr.sr_interpret_f H e1) (sr.sr_interpret_f H e2)))) /\
       (!e1 e2. sr.sr_symbols_f (sr.sr_mk_exp_eq_f e1 e2) =
         sr.sr_symbols_f e1 UNION sr.sr_symbols_f e2))
`;
val symb_mk_exp_conj_f_sound_def = Define `
    symb_mk_exp_conj_f_sound sr =
      ((!e1 e2 H.
         (symb_interpr_welltyped sr H) ==>
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
    ((!e1 e2 conj1 H.
       (symb_interpr_welltyped sr H) ==>
       (sr.sr_interpret_f H (symb_expr_conj_eq sr e1 e2 conj1) = SOME sr.sr_val_true) =
       ((sr.sr_interpret_f H conj1 = SOME sr.sr_val_true) /\
        (sr.sr_interpret_f H e1 <> NONE) /\
        (OPTREL sr.sr_val_eq (sr.sr_interpret_f H e1) (sr.sr_interpret_f H e2)))) /\
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




(*
ASBTRACT SUBSTITUTION OF SYMBOLS FOR EXPRESSIONS IN EXPRESSIONS
=======================================================
[x*3/a] a + 4 = x*3 + 4
*)
val symb_subst_f_sound_def = Define `
    symb_subst_f_sound sr =
      (!symb symb_inst symbexp symbexp_r.
       (!H H' v.
          (sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb)) ==>
          (sr.sr_subst_f (symb, symb_inst) symbexp = symbexp_r) ==>
          (* btw., this means that: "sr.sr_typeof_exp symbexp = sr.sr_typeof_exp symbexp_r" *)

          (sr.sr_interpret_f H symb_inst = SOME v) ==>
          ((symb_interpr_update H (symb, SOME v)) = H') ==>

          (sr.sr_interpret_f H  symbexp_r =
           sr.sr_interpret_f H' symbexp)) /\
       ((sr.sr_subst_f (symb, symb_inst) symbexp = symbexp_r) ==>
        (sr.sr_symbols_f symbexp_r = ((sr.sr_symbols_f symbexp) DIFF {symb}) UNION
           (if symb IN (sr.sr_symbols_f symbexp) then sr.sr_symbols_f symb_inst else EMPTY)))
      )
`;

val symb_subst_store_sound_thm = store_thm(
   "symb_subst_store_sound_thm", ``
!sr.
!H H' symb symb_inst store store_r cstore v.
  (symb_subst_f_sound sr) ==>

  (sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb)) ==>
  (symb_subst_store sr (symb, symb_inst) store = store_r) ==>

  (sr.sr_interpret_f H symb_inst = SOME v) ==>
  ((symb_interpr_update H (symb, SOME v)) = H') ==>

  (symb_interpr_symbstore sr H  store_r cstore =
   symb_interpr_symbstore sr H' store   cstore)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_subst_store_thm, symb_interpr_symbstore_def] >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Cases_on `store' var` >- (
      METIS_TAC [symb_subst_store_thm, optionTheory.option_CLAUSES]
    ) >>

    `store_r var = SOME (sr.sr_subst_f (symb,symb_inst) x)` by (
      METIS_TAC [symb_subst_store_thm]
    ) >>
    FULL_SIMP_TAC std_ss [symb_subst_store_thm, symb_interpr_symbstore_def] >>

    `sr.sr_interpret_f H (sr.sr_subst_f (symb,symb_inst) x) = sr.sr_interpret_f H' x` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>

    METIS_TAC [optionTheory.option_CLAUSES]
  )
);

val symb_subst_store_symbols_thm = store_thm(
   "symb_subst_store_symbols_thm", ``
!sr.
!H symb symb_inst store.
  (symb_subst_f_sound sr) ==>

  (sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H) ==>
  (symb_symbols_store sr store SUBSET symb_interpr_dom H) ==>
  (symb_symbols_store sr (symb_subst_store sr (symb,symb_inst) store) SUBSET symb_interpr_dom H)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_subst_store_def, symb_symbols_store_def, BIGUNION_SUBSET] >>
  REPEAT STRIP_TAC >>

  `(sr.sr_symbols_f symbexp = sr.sr_symbols_f z DIFF {symb} UNION (if symb IN sr.sr_symbols_f z then sr.sr_symbols_f symb_inst else EMPTY))` by (
    METIS_TAC [symb_subst_f_sound_def]
  ) >>

  `sr.sr_symbols_f z SUBSET
        symb_interpr_dom H` by (
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [UNION_SUBSET, GSYM DELETE_DEF, GSYM SUBSET_INSERT_DELETE] >>
  METIS_TAC [SUBSET_REFL, SUBSET_TRANS, INSERT_SUBSET, EMPTY_SUBSET]
);

val symb_subst_store_symbols_thm2 = store_thm(
   "symb_subst_store_symbols_thm2", ``
!sr.
!H symb symb_inst store.
  (symb_subst_f_sound sr) ==>

  (symb IN symb_interpr_dom H) ==>
  (symb_symbols_store sr (symb_subst_store sr (symb,symb_inst) store) SUBSET symb_interpr_dom H) ==>
  (symb_symbols_store sr store SUBSET symb_interpr_dom H)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_subst_store_def, symb_symbols_store_def, BIGUNION_SUBSET] >>
  REPEAT STRIP_TAC >>

  `(sr.sr_symbols_f symbexp DIFF {symb} UNION (if symb IN sr.sr_symbols_f symbexp then sr.sr_symbols_f symb_inst else EMPTY))SUBSET
        symb_interpr_dom H` by (
    METIS_TAC [symb_subst_f_sound_def]
  ) >>
  FULL_SIMP_TAC std_ss [UNION_SUBSET, GSYM DELETE_DEF, GSYM SUBSET_INSERT_DELETE] >>
  METIS_TAC [SUBSET_REFL, SUBSET_TRANS, INSERT_SUBSET]
);

val symb_subst_store_symbols_thm3 = store_thm(
   "symb_subst_store_symbols_thm3", ``
!sr.
!H symb symb_inst store.
  (symb_subst_f_sound sr) ==>

  (symb_symbols_store sr (symb_subst_store sr (symb,symb_inst) store) =
   (symb_symbols_store sr store DIFF {symb}) UNION (if symb IN symb_symbols_store sr store then sr.sr_symbols_f symb_inst else EMPTY))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [symb_subst_store_def, symb_symbols_store_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM EXTENSION] >>
    REPEAT STRIP_TAC >>

    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss) [] >>

    `sr.sr_symbols_f symbexp = (sr.sr_symbols_f z DIFF {symb}) UNION (if symb IN sr.sr_symbols_f z then sr.sr_symbols_f symb_inst else EMPTY)` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>

    CASE_TAC >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >- (
        METIS_TAC []
      ) >>
      Cases_on `symb IN sr.sr_symbols_f z` >> (
        FULL_SIMP_TAC (std_ss) [NOT_IN_EMPTY]
      )
    ) >>
    METIS_TAC []
  ) >>


  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM EXTENSION] >>
  STRIP_TAC >- (
    `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) symbexp) =
       (sr.sr_symbols_f symbexp DIFF {symb}) UNION (if symb IN sr.sr_symbols_f symbexp then sr.sr_symbols_f symb_inst else EMPTY)` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>
    Q.EXISTS_TAC `(sr.sr_symbols_f symbexp DIFF {symb}) UNION (if symb IN sr.sr_symbols_f symbexp then sr.sr_symbols_f symb_inst else EMPTY)` >>
    FULL_SIMP_TAC (std_ss) [] >>

    CASE_TAC >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      Q.EXISTS_TAC `sr.sr_subst_f (symb,symb_inst) symbexp` >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      METIS_TAC []
    )
  ) >>

  Cases_on `?s. symb IN s ∧
              ?symbexp.
                s = sr.sr_symbols_f symbexp /\ ?var. store' var = SOME symbexp` >- (
    FULL_SIMP_TAC std_ss [] >>
    `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) symbexp) =
       (sr.sr_symbols_f symbexp DIFF {symb}) UNION (if symb IN sr.sr_symbols_f symbexp then sr.sr_symbols_f symb_inst else EMPTY)` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>
    Q.EXISTS_TAC `(sr.sr_symbols_f symbexp DIFF {symb}) UNION (if symb IN sr.sr_symbols_f symbexp then sr.sr_symbols_f symb_inst else EMPTY)` >>
    FULL_SIMP_TAC (std_ss) [] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    Q.EXISTS_TAC `sr.sr_subst_f (symb,symb_inst) symbexp` >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ) >>
  METIS_TAC [NOT_IN_EMPTY]
);



val symb_subst_symbols_thm = store_thm(
   "symb_subst_symbols_thm", ``
!sr.
!H symb symb_inst sys.
  (symb_subst_f_sound sr) ==>

  (symb_symbols sr (symb_subst sr (symb, symb_inst) sys) =
   (symb_symbols sr sys DIFF {symb}) UNION (if symb IN symb_symbols sr sys then sr.sr_symbols_f symb_inst else EMPTY))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [symb_subst_def, symb_symbols_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION, symb_symbst_store_def, symb_symbst_pcond_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss) [symb_subst_store_symbols_thm3] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC (std_ss) []
    ) >- (
      Cases_on `symb IN symb_symbols_store sr (symb_symbst_store sys)` >> (
        FULL_SIMP_TAC (std_ss) [NOT_IN_EMPTY]
      )
    ) >>

    `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) (symb_symbst_pcond sys)) =
       (sr.sr_symbols_f (symb_symbst_pcond sys) DIFF {symb}) UNION (if symb IN sr.sr_symbols_f (symb_symbst_pcond sys) then sr.sr_symbols_f symb_inst else EMPTY)` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    Cases_on `symb IN sr.sr_symbols_f (symb_symbst_pcond sys)` >> (
      FULL_SIMP_TAC (std_ss) [NOT_IN_EMPTY]
    )
  ) >>


  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM EXTENSION] >>
  STRIP_TAC >> (
      FULL_SIMP_TAC (std_ss) []
  ) >- (
    `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) (symb_symbst_pcond sys)) =
       (sr.sr_symbols_f (symb_symbst_pcond sys) DIFF {symb}) UNION (if symb IN sr.sr_symbols_f (symb_symbst_pcond sys) then sr.sr_symbols_f symb_inst else EMPTY)` by (
      METIS_TAC [symb_subst_f_sound_def]
    ) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
  ) >>

  Cases_on `symb IN symb_symbols_store sr (symb_symbst_store sys) \/
            symb IN sr.sr_symbols_f (symb_symbst_pcond sys)` >> (
      FULL_SIMP_TAC (std_ss) [NOT_IN_EMPTY]
  ) >>

  `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) (symb_symbst_pcond sys)) =
     (sr.sr_symbols_f (symb_symbst_pcond sys) DIFF {symb}) UNION (if symb IN sr.sr_symbols_f (symb_symbst_pcond sys) then sr.sr_symbols_f symb_inst else EMPTY)` by (
    METIS_TAC [symb_subst_f_sound_def]
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
);



val symb_subst_suitable_interpretation_thm = store_thm(
   "symb_subst_suitable_interpretation_thm", ``
!sr.
!sys H symb symb_inst.
  (symb_subst_f_sound sr) ==>

  (sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H) ==>
  (symb_suitable_interpretation sr sys H) ==>
  (symb_suitable_interpretation sr (symb_subst sr (symb,symb_inst) sys) H)
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def,
     symb_interpr_for_symbs_def, symb_symbols_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_subst_def, symb_symbst_pcond_def, symb_symbst_store_def] >>

  `symb_symbols_store sr (symb_subst_store sr (symb,symb_inst) f) SUBSET
        symb_interpr_dom H` by (
    METIS_TAC [symb_subst_store_symbols_thm, UNION_SUBSET]
  ) >>

  `sr.sr_symbols_f (sr.sr_subst_f (symb,symb_inst) c) SUBSET
        symb_interpr_dom H` by (
    `(sr.sr_symbols_f c DIFF {symb} UNION (sr.sr_symbols_f symb_inst)) SUBSET symb_interpr_dom H` by (
      METIS_TAC [UNION_SUBSET, DIFF_SUBSET, SUBSET_TRANS]
    ) >>
    `(sr.sr_symbols_f c DIFF {symb}) SUBSET symb_interpr_dom H` by (
      METIS_TAC [UNION_SUBSET, DIFF_SUBSET, SUBSET_TRANS]
    ) >>
    Cases_on `symb IN sr.sr_symbols_f c` >> (
      METIS_TAC [symb_subst_f_sound_def, UNION_EMPTY]
    )
  ) >>

  METIS_TAC [UNION_SUBSET]
);

val symb_subst_suitable_interpretation_thm2 = store_thm(
   "symb_subst_suitable_interpretation_thm2", ``
!sr.
!sys H symb symb_inst.
  (symb_subst_f_sound sr) ==>

  (symb IN symb_interpr_dom H) ==>
  (symb_suitable_interpretation sr (symb_subst sr (symb,symb_inst) sys) H) ==>
  (symb_suitable_interpretation sr sys H)
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def,
     symb_interpr_for_symbs_def, symb_symbols_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_subst_def, symb_symbst_pcond_def, symb_symbst_store_def, UNION_SUBSET] >>

  STRIP_TAC >- (
    METIS_TAC [symb_subst_store_symbols_thm2]
  ) >>

  `(sr.sr_symbols_f c DIFF {symb} UNION (if symb IN sr.sr_symbols_f c then sr.sr_symbols_f symb_inst else EMPTY)) SUBSET symb_interpr_dom H` by (
    METIS_TAC [symb_subst_f_sound_def]
  ) >>
  FULL_SIMP_TAC std_ss [UNION_SUBSET, GSYM DELETE_DEF, GSYM SUBSET_INSERT_DELETE] >>
  METIS_TAC [SUBSET_REFL, SUBSET_TRANS, INSERT_SUBSET]
);

val symb_subst_suitable_interpretation_thm3 = store_thm(
   "symb_subst_suitable_interpretation_thm3", ``
!sr.
!sys H symb symb_inst vo.
  (symb_subst_f_sound sr) ==>

  (sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H) ==>

  (symb_suitable_interpretation sr sys  (symb_interpr_update H (symb, vo))) ==>
  (symb_suitable_interpretation sr (symb_subst sr (symb, symb_inst) sys) H)
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_subst_symbols_thm] >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  CONJ_TAC >- (
    Cases_on `vo` >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_dom_UPDATE_NONE_thm, symb_interpr_dom_UPDATE_SOME_thm]
    ) >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DELETE, GSYM DELETE_DEF] >>
      METIS_TAC [DELETE_NON_ELEMENT]
    ) >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [DELETE_SUBSET_INSERT, GSYM DELETE_DEF]
  ) >>

  Cases_on `symb IN symb_symbols sr sys` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
  )
);

val symb_subst_suitable_interpretation_thm4 = store_thm(
   "symb_subst_suitable_interpretation_thm4", ``
!sr.
!sys H symb symb_inst vo.
  (symb_subst_f_sound sr) ==>

  (symb_suitable_interpretation sr (symb_subst sr (symb, symb_inst) sys) H) ==>
  (symb_suitable_interpretation sr sys  (symb_interpr_update H (symb, SOME v)))
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_subst_symbols_thm] >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Cases_on `symb IN symb_symbols sr sys` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_dom_UPDATE_NONE_thm, symb_interpr_dom_UPDATE_SOME_thm]
  ) >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [DELETE_SUBSET_INSERT, GSYM DELETE_DEF]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DELETE, GSYM DELETE_DEF] >>
  METIS_TAC [DELETE_NON_ELEMENT]
);

val symb_subst_sound_thm1 = store_thm(
   "symb_subst_sound_thm1", ``
!sr.
!H H' symb symb_inst sys sys_r s v.
  (symb_typeof_exp_sound sr) ==>
  (symb_subst_f_sound sr) ==>

  (* can remove this assumption with case analysis on "~(symb IN symb_symbols sr sys)" and symbol set argument *)
  (sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H) ==>
  (*(symb_interpr_get H symb = SOME v') ==>
    (sr.sr_typeof_symb symb = sr.sr_typeof_val v') ==>*)

  (sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb)) ==>
  (symb_subst sr (symb, symb_inst) sys = sys_r) ==>

  (sr.sr_interpret_f H symb_inst = SOME v) ==>
  ((symb_interpr_update H (symb, SOME v)) = H') ==>

  (symb_matchstate sr sys_r H  s) ==>
  (symb_matchstate sr sys   H' s)
``,
  REPEAT STRIP_TAC >>

(*
  (* can remove this assumption with case analysis on "~(symb IN symb_symbols sr sys)" and symbol set argument *)
  Cases_on `~(symb IN symb_symbols sr sys)` >- (
    `sys_r = sys` by (
      cheat
    ) >>
    FULL_SIMP_TAC (std_ss) [] >>
    cheat
  ) >>

  `(sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H)` by (
    `sr.sr_symbols_f symb_inst SUBSET symb_symbols sr sys_r` by (
      PAT_X_ASSUM ``symb_subst sr (symb,symb_inst) sys = sys_r`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss) [symb_subst_symbols_thm] >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ) >>
    FULL_SIMP_TAC (std_ss) [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
    METIS_TAC [SUBSET_TRANS]
  ) >>
*)

  Cases_on `sys_r` >>
  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [symb_subst_def, symb_matchstate_def] >>

  (
    FULL_SIMP_TAC std_ss [symb_symbst_pc_def, symb_symbst_extra_def,
        symb_symbst_store_def] >>
    STRIP_TAC >>
    REPEAT STRIP_TAC >| [
      ALL_TAC
    ,
      (*  `(sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H)` by cheat >>*)
      METIS_TAC [symb_interpr_update_interpret_f_IMP_welltyped_thm,
                 symb_interpr_update_SOME_IMP_welltyped_thm2]
    ,
      METIS_TAC [symb_subst_store_sound_thm]
    ,
      METIS_TAC [symb_interpr_symbpcond_def, symb_subst_f_sound_def, symb_symbst_pcond_def]
    ]
  ) >>
  METIS_TAC [symb_subst_suitable_interpretation_thm4, symb_subst_def]
);

val symb_subst_sound_thm2 = store_thm(
   "symb_subst_sound_thm2", ``
!sr.
!H H' symb symb_inst sys sys_r s v.
  (symb_typeof_exp_sound sr) ==>
  (symb_subst_f_sound sr) ==>

  (sr.sr_symbols_f symb_inst SUBSET symb_interpr_dom H) ==> (* need this for symb_suitable_interpretation *)
  (*(symb_interpr_get H symb = SOME v') ==>
    (sr.sr_typeof_symb symb = sr.sr_typeof_val v') ==>*)
  (!v'. symb_interpr_get H symb = SOME v' ==> sr.sr_typeof_symb symb = sr.sr_typeof_val v') ==> (* need this for symb_interpr_welltyped *)

  (sr.sr_typeof_exp symb_inst = SOME (sr.sr_typeof_symb symb)) ==>
  (symb_subst sr (symb, symb_inst) sys = sys_r) ==>

  (sr.sr_interpret_f H symb_inst = SOME v) ==>
  ((symb_interpr_update H (symb, SOME v)) = H') ==>

  (symb_matchstate sr sys   H' s) ==>
  (symb_matchstate sr sys_r H  s)
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys_r` >>
  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [symb_subst_def, symb_matchstate_def] >>

  (
    FULL_SIMP_TAC std_ss [symb_symbst_pc_def, symb_symbst_extra_def,
        symb_symbst_store_def] >>
    STRIP_TAC >>
    REPEAT STRIP_TAC >| [
      ALL_TAC
    ,
      Cases_on `symb_interpr_get H symb` >> (
        METIS_TAC [symb_interpr_update_interpret_f_IMP_welltyped_thm,
                   symb_interpr_update_SOME_IMP_welltyped_thm2,
                   symb_interpr_update_SOME_IMP_welltyped_thm3])
    ,
      METIS_TAC [symb_subst_store_sound_thm]
    ,
      METIS_TAC [symb_interpr_symbpcond_def, symb_subst_f_sound_def, symb_symbst_pcond_def]
    ]
  ) >>
  METIS_TAC [symb_subst_suitable_interpretation_thm3, symb_subst_def]
);



(*
GOAL: SINGLE STEP SOUNDNESS
=======================================================
*)
(* this definition assumes that the concrete transition function is total,
   if it wasn't we needed more here and also needed to take special care *)
val symb_step_sound_def = Define `
  symb_step_sound sr =
    (!sys Pi.
     (sr.sr_step_symb sys = Pi) ==>
     (!s H s'.
       (symb_matchstate sr sys H s) ==>
       (sr.sr_step_conc s = s') ==>
       (?sys'. sys' IN Pi /\ symb_matchstate sr sys' H s')
     )
    )
`;

val _ = export_theory();
