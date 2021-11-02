open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;
open combinTheory;

open symb_interpretTheory;

val _ = new_theory "symb_record";


(*
RECORD FOR REPRESENTING GENERIC CONCRETE AND SYMBOLIC TRANSITION SYSTEM
=======================================================
*)
val _ = Datatype `symb_concst_t =
   SymbConcSt 'a_label ('b_var -> 'c_val option) 'd_extra
`;
val symb_concst_pc_def = Define `
  symb_concst_pc (SymbConcSt lbl _ _) = lbl
`;
val symb_concst_store_def = Define `
  symb_concst_store (SymbConcSt _ store _) = store
`;
val symb_concst_extra_def = Define `
  symb_concst_extra (SymbConcSt _ _ extra) = extra
`;
(*
``SymbConcSt (0w:word64) (K (SOME "hallo"))``
*)

val _ = Datatype `symb_symbst_t =
   SymbSymbSt 'a_label ('b_var -> 'c_symbexpr option) 'c_symbexpr 'd_extra
`;
val symb_symbst_pc_def = Define `
  symb_symbst_pc (SymbSymbSt lbl _ _ _) = lbl
`;
val symb_symbst_store_def = Define `
  symb_symbst_store (SymbSymbSt _ store _ _) = store
`;
val symb_symbst_store_update_def = Define `
  symb_symbst_store_update var symbexpr (SymbSymbSt lbl store pcond extra) =
    SymbSymbSt lbl ((var =+ (SOME symbexpr)) store) pcond extra
`;
val symb_symbst_pcond_def = Define `
  symb_symbst_pcond (SymbSymbSt _ _ pcond _) = pcond
`;
val symb_symbst_pcond_update_def = Define `
  symb_symbst_pcond_update pcond_f (SymbSymbSt lbl store pcond extra) =
    SymbSymbSt lbl store (pcond_f pcond) extra
`;
val symb_symbst_extra_def = Define `
  symb_symbst_extra (SymbSymbSt _ _ _ extra) = extra
`;


val symb_symbst_store_update_READ_thm = store_thm(
   "symb_symbst_store_update_READ_thm", ``
!var1 var2 symbexp sys.
  (symb_symbst_store (symb_symbst_store_update var1 symbexp sys) var2 =
   if var1 = var2 then SOME symbexp else symb_symbst_store sys var2)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_update_def, symb_symbst_store_def, APPLY_UPDATE_THM]
);
val symb_symbst_store_update_UNCHANGED_thm = store_thm(
   "symb_symbst_store_update_UNCHANGED_thm", ``
!var symbexp sys.
  (symb_symbst_pc (symb_symbst_store_update var symbexp sys) = symb_symbst_pc sys) /\
  (symb_symbst_pcond (symb_symbst_store_update var symbexp sys) = symb_symbst_pcond sys) /\
  (symb_symbst_extra (symb_symbst_store_update var symbexp sys) = symb_symbst_extra sys)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_update_def, symb_symbst_pc_def, symb_symbst_pcond_def, symb_symbst_extra_def]
);

val symb_symbst_pcond_update_READ_thm = store_thm(
   "symb_symbst_pcond_update_READ_thm", ``
!pcond_f sys.
  (symb_symbst_pcond (symb_symbst_pcond_update pcond_f sys) =
   pcond_f (symb_symbst_pcond sys))
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_symbst_pcond_def]
);
val symb_symbst_pcond_update_UNCHANGED_thm = store_thm(
   "symb_symbst_pcond_update_UNCHANGED_thm", ``
!pcond_f sys.
  (symb_symbst_pc (symb_symbst_pcond_update pcond_f sys) = symb_symbst_pc sys) /\
  (symb_symbst_store (symb_symbst_pcond_update pcond_f sys) = symb_symbst_store sys) /\
  (symb_symbst_extra (symb_symbst_pcond_update pcond_f sys) = symb_symbst_extra sys)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_extra_def]
);


(*
NOTION: INSTANTIATION DATATYPE (SYMB RECORD)
=======================================================
*)
val _ = Datatype `symb_rec_t =
   <|
      (* required symbolic expression building blocks *)
      sr_val_true        : 'c_val;

      sr_mk_exp_symb_f   : 'e_symbol -> 'f_symbexpr;
      sr_mk_exp_conj_f   : 'f_symbexpr -> 'f_symbexpr -> 'f_symbexpr;
      sr_mk_exp_eq_f     : 'f_symbexpr -> 'f_symbexpr -> 'f_symbexpr;

      sr_subst_f         : ('e_symbol # 'f_symbexpr) -> 'f_symbexpr -> 'f_symbexpr;

      (* symbols of symbolic exepressions *)
      sr_symbols_f       : 'f_symbexpr ->
                           ('e_symbol -> bool);

      (* type business *)
      (* this is needed to enable more nuanced/useful simplifications (PART I) as well the INST rule (PART II) *)
      (* val and symb types allow us to have
         - a notion of well typed-interpretations (use in state matching) (PART I)
         - (PART II) require interpret_f to return SOME in case the interpretation contains all symbols_f symbols with correspondingly typed values (needed for INST rule to use semantically defined substitution) (works only under the assumption that the expression has a type, then the value that is interprets to is of that type)
      *)
      sr_typeof_val      : 'c_val -> 'g_type;
      sr_typeof_symb     : 'e_symbol -> 'g_type;
      sr_typeof_exp      : 'f_symbexpr -> ('g_type option);
      (* need a default value function to be able to assign arbitrary values in CONS and SUBST rule *)
      sr_ARB_val         : 'g_type -> 'c_val;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     : (('e_symbol, 'c_val) symb_interpret_t) ->
                           'f_symbexpr ->
                           'c_val option;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       : (('a_label, 'b_var, 'c_val, 'd_extra) symb_concst_t) ->
                           (('a_label, 'b_var, 'c_val, 'd_extra) symb_concst_t);

      sr_step_symb       : (('a_label, 'b_var, 'f_symbexpr, 'd_extra) symb_symbst_t) ->
                           ((('a_label, 'b_var, 'f_symbexpr, 'd_extra) symb_symbst_t) ->
                           bool);
   |>`;


(*
NOTION: SYMBOL DEPENDENCE FOR STORE AND STATE AND SET OF STATES
=======================================================
*)

val symb_symbols_store_def = Define `
    symb_symbols_store sr store =
      BIGUNION ({sr.sr_symbols_f symbexp | ?var. store var = SOME symbexp})
`;
val symb_symbols_def = Define `
    symb_symbols sr sys =
      (symb_symbols_store sr (symb_symbst_store sys) UNION
       sr.sr_symbols_f (symb_symbst_pcond sys))
`;

val symb_symbols_SUBSET_pcond_thm = store_thm(
   "symb_symbols_SUBSET_pcond_thm", ``
!sr.
!sys.
  (sr.sr_symbols_f (symb_symbst_pcond sys))
  SUBSET
  (symb_symbols sr sys)
``,
  METIS_TAC [symb_symbols_def, SUBSET_UNION]
);

val symb_symbols_SUBSET_store_thm = store_thm(
   "symb_symbols_SUBSET_store_thm", ``
!sr.
!sys.
  (symb_symbols_store sr (symb_symbst_store sys))
  SUBSET
  (symb_symbols sr sys)
``,
  METIS_TAC [symb_symbols_def, SUBSET_UNION]
);

val symb_symbols_SUBSET_store_exps_thm = store_thm(
   "symb_symbols_SUBSET_store_exps_thm", ``
!sr.
!store var symbexp.
  ((store var) = SOME symbexp) ==>
  ((sr.sr_symbols_f symbexp)
   SUBSET
   (symb_symbols_store sr store))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_symbols_store_def, SUBSET_DEF] >>
  METIS_TAC []
);

val symb_symbols_SUBSET_store_exps_thm2 = store_thm(
   "symb_symbols_SUBSET_store_exps_thm2", ``
!sr.
!sys var symbexp.
  (((symb_symbst_store sys) var) = SOME symbexp) ==>
  ((sr.sr_symbols_f symbexp)
   SUBSET
   (symb_symbols sr sys))
``,
  METIS_TAC [symb_symbols_def, symb_symbols_SUBSET_store_exps_thm, symb_symbols_SUBSET_store_thm, UNION_SUBSET, SUBSET_TRANS]
);

val symb_symbols_set_def = Define `
    symb_symbols_set sr Pi =
      BIGUNION ({symb_symbols sr sys | sys IN Pi})
`;

val symb_symbols_set_SUBSET_thm = store_thm(
   "symb_symbols_set_SUBSET_thm", ``
!sr.
!sys Pi.
  (sys IN Pi) ==>
  ((symb_symbols sr sys) SUBSET (symb_symbols_set sr Pi))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_symbols_set_def, BIGUNION, SUBSET_DEF] >>
  METIS_TAC []
);

val symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2 = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2", ``
!sr.
!var symbexp sys.
  (sr.sr_symbols_f symbexp) SUBSET (symb_symbols sr (symb_symbst_store_update var symbexp sys))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbols_store_def] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbols_store_def, SUBSET_DEF] >>

  METIS_TAC [APPLY_UPDATE_THM]
);

val symb_symbols_of_symb_symbst_store_update_SUBSET1_thm = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET1_thm", ``
!sr.
!var symbexp sys.
  ((symb_symbols sr (symb_symbst_store_update var symbexp sys)) SUBSET
   ((symb_symbols sr sys) UNION (sr.sr_symbols_f symbexp)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>

  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, BIGUNION_SUBSET] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, SUBSET_DEF] >>

    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >- (
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    ) >>

    METIS_TAC [APPLY_UPDATE_THM]
  ) >>

  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_store_update_SUBSET2_thm = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET2_thm", ``
!sr.
!var symbexp symbexp' sys.
  ((symb_symbst_store sys) var = SOME symbexp') ==>
  ((symb_symbols sr sys) SUBSET
   ((symb_symbols sr (symb_symbst_store_update var symbexp sys)) UNION
    (sr.sr_symbols_f (symbexp')))
  )
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>

  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, BIGUNION_SUBSET] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, SUBSET_DEF] >>

    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >- (
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss []
    ) >>

    METIS_TAC [APPLY_UPDATE_THM]
  ) >>

  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm = store_thm(
   "symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm", ``
!sr.
!pcond_f sys.
  ((symb_symbols sr (symb_symbst_pcond_update pcond_f sys)) SUBSET
   ((symb_symbols sr sys) UNION (sr.sr_symbols_f (pcond_f (symb_symbst_pcond sys)))))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_pcond_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>
  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm = store_thm(
   "symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm", ``
!sr.
!pcond_f sys.
  ((symb_symbols sr sys) SUBSET
   ((symb_symbols sr (symb_symbst_pcond_update pcond_f sys)) UNION
    (sr.sr_symbols_f (symb_symbst_pcond sys)))
  )
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_pcond_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>
  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

(*
NOTATION: WELL-TYPED INTERPRETATION
=======================================================
*)
val symb_interpr_welltyped_def = Define `
    symb_interpr_welltyped sr H =
      (!symb.
         (symb IN symb_interpr_dom H) ==>
         (?v. symb_interpr_get H symb = SOME v /\
              sr.sr_typeof_symb symb = sr.sr_typeof_val v))
`;

val symb_interpr_welltyped_thm = store_thm(
   "symb_interpr_welltyped_thm", ``
!sr.
!H.
  (symb_interpr_welltyped sr H) =
  (!symb v.
    (symb_interpr_get H symb = SOME v) ==>
    (sr.sr_typeof_symb symb = sr.sr_typeof_val v))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def, symb_interpr_dom_thm] >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Cases_on `symb_interpr_get H symb` >> (
      FULL_SIMP_TAC std_ss [optionTheory.NOT_NONE_SOME] >>
      METIS_TAC [optionTheory.option_CLAUSES]
    )
  )
);

val symb_interpr_ext_welltyped_IMP_thm = store_thm(
   "symb_interpr_ext_welltyped_IMP_thm", ``
!sr.
!H1 H2.
  (symb_interpr_ext H2 H1) ==>
  (symb_interpr_welltyped sr H2) ==>
  (symb_interpr_welltyped sr H1)
``,
  FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def, symb_interpr_welltyped_def] >>
  METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, symb_interpr_dom_thm]
);

val symb_interpr_extend_welltyped_IMP_thm = store_thm(
   "symb_interpr_extend_welltyped_IMP_thm", ``
!sr.
!H_base H_extra.
  (symb_interpr_welltyped sr H_base) ==>
  (symb_interpr_welltyped sr H_extra) ==>
  (symb_interpr_welltyped sr (symb_interpr_extend H_extra H_base))
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interprs_eq_for_def,
     symb_interpr_welltyped_def, symb_interpr_extend_def,
     symb_interpr_dom_def, symb_interpr_get_def] >>

  Cases_on `symb IN symb_interpr_dom H_base` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_interpr_ext_def, symb_interprs_eq_for_def,
       symb_interpr_welltyped_def, symb_interpr_extend_def,
       symb_interpr_dom_def, symb_interpr_get_def]
  ) >>

  METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm]
);

val symb_interpr_update_NONE_IMP_welltyped_thm = store_thm(
   "symb_interpr_update_NONE_IMP_welltyped_thm", ``
!sr.
!H symb.
  (symb_interpr_welltyped sr H) ==>
  (symb_interpr_welltyped sr (symb_interpr_update H (symb,NONE)))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [symb_interpr_welltyped_def, symb_interpr_get_update_thm,
               symb_interpr_dom_UPDATE_NONE_thm] >>
  REPEAT STRIP_TAC >>
  `symb <> symb'` by (
    METIS_TAC [ELT_IN_DELETE]
  ) >>

  FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def] >>
  METIS_TAC [DELETE_SUBSET, SUBSET_DEF]
);

val symb_interpr_update_SOME_IMP_welltyped_thm = store_thm(
   "symb_interpr_update_SOME_IMP_welltyped_thm", ``
!sr.
!H symb v.
  (symb_interpr_welltyped sr H) ==>
  (sr.sr_typeof_symb symb = sr.sr_typeof_val v) ==>
  (symb_interpr_welltyped sr (symb_interpr_update H (symb, SOME v)))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [symb_interpr_welltyped_def, symb_interpr_get_update_thm,
               symb_interpr_dom_UPDATE_SOME_thm] >>
  REPEAT STRIP_TAC >>
  Cases_on `symb = symb'` >> (
    FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def, IN_INSERT]
  )
);

val symb_interpr_update_SOME_IMP_welltyped_thm2 = store_thm(
   "symb_interpr_update_SOME_IMP_welltyped_thm2", ``
!sr.
!H symb vo v.
  (symb_interpr_get H symb = SOME v) ==>
  (symb_interpr_welltyped sr (symb_interpr_update H (symb, vo))) ==>
  (sr.sr_typeof_symb symb = sr.sr_typeof_val v) ==>
  (symb_interpr_welltyped sr H)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def, symb_interpr_get_update_thm] >>
  REPEAT STRIP_TAC >>
  Cases_on `symb = symb'` >> (
    FULL_SIMP_TAC std_ss [symb_interpr_welltyped_def, IN_INSERT]
  ) >>

  Cases_on `vo` >> (
    FULL_SIMP_TAC std_ss [symb_interpr_dom_UPDATE_NONE_thm,
       symb_interpr_dom_UPDATE_SOME_thm, IN_DELETE, IN_INSERT]
  ) >>

  METIS_TAC []
);





(*
NOTATION: INTERPRETATION OF SYMBOLIC STATES AND SYMBOLIC PATH CONDITIONS
=======================================================
*)
val symb_interpr_symbstore_def = Define `
  symb_interpr_symbstore sr H store cstore =
    (!var. (store var <> NONE \/ cstore var <> NONE) ==>
         ?symbexp v.
            store  var = SOME symbexp /\
            cstore var = SOME v /\
            sr.sr_interpret_f H symbexp = SOME v)
`;

val symb_symbst_store_update_IMP_EQ_thm = store_thm(
   "symb_symbst_store_update_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 var symbexp symbexp' cstore.
  ((symb_symbst_store sys1) var = SOME symbexp) ==>
  (sys2 = symb_symbst_store_update var symbexp' sys1) ==>

  (sr.sr_interpret_f H symbexp =
   sr.sr_interpret_f H symbexp') ==>

  ((symb_interpr_symbstore sr H (symb_symbst_store sys1) cstore) =
   (symb_interpr_symbstore sr H (symb_symbst_store sys2) cstore))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def] >>

  (* proof as two implications considering all variables var' *)
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >> (
      PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPEC `var'`)) >>
      FULL_SIMP_TAC std_ss [symb_symbst_store_update_READ_thm] >>
      REV_FULL_SIMP_TAC std_ss []
    )
  )
);

val symb_interpr_symbpcond_def = Define `
  symb_interpr_symbpcond sr H sys =
    (sr.sr_interpret_f H (symb_symbst_pcond sys) = SOME sr.sr_val_true)
`;

val symb_symbst_pcond_IMP_EQ_thm = store_thm(
   "symb_symbst_pcond_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 s.
  (symb_symbst_pcond sys1 = symb_symbst_pcond sys2) ==>
  ((symb_interpr_symbpcond sr H sys1) =
   (symb_interpr_symbpcond sr H sys2))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def]
);

val symb_symbst_pcond_update_IMP_EQ_thm = store_thm(
   "symb_symbst_pcond_update_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 pcond pcond_f.
  (symb_symbst_pcond sys1 = pcond) ==>
  (sys2 = symb_symbst_pcond_update pcond_f sys1) ==>

  (sr.sr_interpret_f H pcond =
   sr.sr_interpret_f H (pcond_f pcond)) ==>

  ((symb_interpr_symbpcond sr H sys1) =
   (symb_interpr_symbpcond sr H sys2))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys1` >>
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def, symb_symbst_pcond_update_READ_thm]
);


(*
NOTATION: STATE MATCHING
=======================================================
*)
val symb_suitable_interpretation_def = Define `
    symb_suitable_interpretation sr sys H =
      symb_interpr_for_symbs (symb_symbols sr sys) H
`;

val symb_suitable_interpretation_SUBSET_dom_thm = store_thm(
   "symb_suitable_interpretation_SUBSET_dom_thm", ``
!sr.
!sys H.
  (symb_suitable_interpretation sr sys H) =
  ((symb_symbols sr sys) SUBSET (symb_interpr_dom H))
``,
  REWRITE_TAC [symb_suitable_interpretation_def, symb_interpr_for_symbs_def]
);

val symb_suitable_interpretation_UPDATE_SOME_thm = store_thm(
   "symb_suitable_interpretation_UPDATE_SOME_thm", ``
!sr.
!sys H symb v.
  (symb_suitable_interpretation sr sys H) ==>
  (symb_suitable_interpretation sr sys (symb_interpr_update H (symb,SOME v)))
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def,
     symb_interpr_for_symbs_def, symb_interpr_dom_UPDATE_SOME_thm] >>
  METIS_TAC [SUBSET_TRANS, SUBSET_INSERT_RIGHT, SUBSET_REFL]
);

val symb_suitable_interpretation_UPDATE_SOME_thm2 = store_thm(
   "symb_suitable_interpretation_UPDATE_SOME_thm2", ``
!sr.
!sys H symb v.
  (symb IN symb_interpr_dom H) ==>
  (symb_suitable_interpretation sr sys (symb_interpr_update H (symb,SOME v))) ==>
  (symb_suitable_interpretation sr sys H)
``,
  FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def,
     symb_interpr_for_symbs_def, symb_interpr_dom_UPDATE_SOME_thm] >>
  METIS_TAC [SUBSET_TRANS, INSERT_SUBSET, SUBSET_REFL]
);

val symb_minimal_interpretation_def = Define `
    symb_minimal_interpretation sr sys H =
      symb_interpr_for_symbs_min (symb_symbols sr sys) H
`;

val symb_minimal_interpretation_EQ_dom_thm = store_thm(
   "symb_minimal_interpretation_EQ_dom_thm", ``
!sr.
!sys H.
  (symb_minimal_interpretation sr sys H) =
  (symb_symbols sr sys = symb_interpr_dom H)
``,
  REWRITE_TAC [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def]
);

local
  val symb_rec_t_tm       = ``: ('a, 'b, 'c, 'd, 'e, 'f, 'g) symb_rec_t``;
  val symb_concst_t_tm    = ``: ('a, 'b, 'c, 'd) symb_concst_t``;
in
  val symb_matchstate_def = Define `
      symb_matchstate ^(mk_var("sr", symb_rec_t_tm))
                      sys
                      H
                      ^(mk_var("s", symb_concst_t_tm)) =
    (symb_suitable_interpretation sr sys H /\
     symb_interpr_welltyped sr H /\
     symb_symbst_pc sys = symb_concst_pc s /\
     symb_interpr_symbstore sr H (symb_symbst_store sys) (symb_concst_store s) /\
     symb_interpr_symbpcond sr H sys /\
     symb_symbst_extra sys = symb_concst_extra s)
`;
end;

val symb_symbst_store_update_IMP_matchstate_EQ_thm = store_thm(
   "symb_symbst_store_update_IMP_matchstate_EQ_thm", ``
!sr.
!H sys1 sys2 var symbexp symbexp' s.
  ((symb_symbst_store sys1) var = SOME symbexp) ==>
  (sys2 = symb_symbst_store_update var symbexp' sys1) ==>

  (((sr.sr_symbols_f symbexp) UNION
    (sr.sr_symbols_f symbexp')) SUBSET (symb_interpr_dom H)) ==>

  (sr.sr_interpret_f H symbexp =
   sr.sr_interpret_f H symbexp') ==>

  ((symb_matchstate sr sys1 H s) =
   (symb_matchstate sr sys2 H s))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_def] >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def, symb_symbst_store_update_UNCHANGED_thm] >>
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
      METIS_TAC
       [symb_symbst_store_update_IMP_EQ_thm, SUBSET_TRANS, UNION_SUBSET,
        symb_symbols_of_symb_symbst_store_update_SUBSET1_thm,
        symb_symbols_of_symb_symbst_store_update_SUBSET2_thm]
    )
  )
);

val symb_symbst_pcond_update_IMP_matchstate_EQ_thm = store_thm(
   "symb_symbst_pcond_update_IMP_matchstate_EQ_thm", ``
!sr.
!H sys1 sys2 pcond pcond_f s.
  (symb_symbst_pcond sys1 = pcond) ==>
  (sys2 = symb_symbst_pcond_update pcond_f sys1) ==>

  (((sr.sr_symbols_f pcond) UNION
    (sr.sr_symbols_f (pcond_f pcond))) SUBSET (symb_interpr_dom H)) ==>

  (sr.sr_interpret_f H pcond =
   sr.sr_interpret_f H (pcond_f pcond)) ==>

  ((symb_matchstate sr sys1 H s) =
   (symb_matchstate sr sys2 H s))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_def] >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_UNCHANGED_thm] >>
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
      METIS_TAC
       [symb_symbst_pcond_update_IMP_EQ_thm, SUBSET_TRANS, UNION_SUBSET,
        symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm,
        symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm,
        symb_symbst_pcond_update_UNCHANGED_thm]
    )
  )
);


(* matching gives a UNIQUE store *)
val symb_matchstate_UNIQUE_store_thm = store_thm(
   "symb_matchstate_UNIQUE_store_thm", ``
!sr.
!sys H s s'.
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate sr sys H s') ==>

  (symb_concst_store s = symb_concst_store s')
``,
  REPEAT GEN_TAC >>
  Cases_on `sys` >> Cases_on `s` >> Cases_on `s'` >>
  FULL_SIMP_TAC (std_ss)
    [symb_matchstate_def,
     symb_interpr_symbstore_def, symb_concst_store_def, symb_symbst_store_def] >>
  REPEAT STRIP_TAC >>

  HO_MATCH_MP_TAC EQ_EXT >> STRIP_TAC >>
  (* show that the concrete store functions are equivalent for all x *)

  REPEAT (PAT_X_ASSUM ``!var. A`` (ASSUME_TAC o (Q.SPEC `x`))) >>

  Cases_on `f x` >> Cases_on `f' x` >> Cases_on `f'' x` >> (
    FULL_SIMP_TAC std_ss []
  )
);

(* matching is unique *)
val symb_matchstate_UNIQUE_thm = store_thm(
   "symb_matchstate_UNIQUE_thm", ``
!sr.
!sys H s s'.
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate sr sys H s') ==>

  (s = s')
``,
  REPEAT GEN_TAC >>
  Cases_on `s` >> Cases_on `s'` >>
  FULL_SIMP_TAC (std_ss) (type_rws ``:('a, 'b, 'c, 'd) symb_concst_t``) >>

  REPEAT STRIP_TAC >- (
    (* first take care of the pc *)
    FULL_SIMP_TAC (std_ss)
      [symb_matchstate_def, symb_concst_pc_def, symb_symbst_pc_def]
  ) >- (
    (* now the concrete store *)
    METIS_TAC [symb_concst_store_def, symb_matchstate_UNIQUE_store_thm]
  ) >>
  (* and now the extra *)
  FULL_SIMP_TAC (std_ss)
    [symb_matchstate_def, symb_concst_extra_def, symb_symbst_extra_def]
);

val symb_matchstate_IMP_interpret_exp_SOME_thm = store_thm(
   "symb_matchstate_IMP_interpret_exp_SOME_thm", ``
!sr.
!sys var symbexp H s.
  (symb_symbst_store sys var = SOME symbexp) ==>

  (symb_matchstate sr sys H s) ==>

  (?v. sr.sr_interpret_f H symbexp = SOME v)
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_def, symb_matchstate_def, symb_interpr_symbstore_def] >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`var`])) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss []
);

val symb_matchstate_ext_IMP_SAME_interpret_exp_thm = store_thm(
   "symb_matchstate_ext_IMP_SAME_interpret_exp_thm", ``
!sr.
!sys var symbexp H H' s v.
  (symb_symbst_store sys var = SOME symbexp) ==>

  (symb_matchstate sr sys H  s) ==>
  (symb_matchstate sr sys H' s) ==>

  (sr.sr_interpret_f H  symbexp =
   sr.sr_interpret_f H' symbexp)
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_def, symb_matchstate_def, symb_interpr_symbstore_def] >>

  REPEAT (PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`var`]))) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss []
);



val symb_matchstate_ext_def = Define `
  symb_matchstate_ext sr sys H s =
    (?H'. symb_interpr_ext H' H /\
          symb_matchstate sr sys H' s)
`;

val symb_matchstate_ext_w_ext_thm = store_thm(
   "symb_matchstate_ext_w_ext_thm", ``
!sr.
!H H' sys s.
  (symb_interpr_ext H' H) ==>

  (symb_matchstate_ext sr sys H' s) ==>
  (symb_matchstate_ext sr sys H  s)
``,
  METIS_TAC [symb_matchstate_ext_def, symb_interpr_ext_TRANS_thm]
);


(*
NOTATION: MULTISTEP WITH LABEL SET
=======================================================
*)

(* n steps deterministic transition relation with using FUNPOW *)
val step_n_def = Define `
  (step_n stepf s n s' = (FUNPOW stepf n s = s'))
`;

val step_n_deterministic_thm = store_thm(
   "step_n_deterministic_thm", ``
!stepf.
!s n s' s''.
(step_n stepf s n s') ==>
(step_n stepf s n s'') ==>
(s' = s'')
``,
  SIMP_TAC std_ss [step_n_def]
);
val step_n_total_thm = store_thm(
   "step_n_total_thm", ``
!stepf.
!s n.
?s'.
step_n stepf s n s'
``,
  SIMP_TAC std_ss [step_n_def]
);

val step_n_in_L_relaxed_def = Define `
  step_n_in_L_relaxed pcf stepf s n L s' =
    (step_n stepf s n s' /\
     (n > 0) /\
     (!n'. 0 < n' ==> n' < n ==>
        ?s''. step_n stepf s n' s'' /\ pcf(s'') IN L))
`;

val step_n_in_L_def = Define `
  step_n_in_L pcf stepf s n L s' =
    ((pcf s) IN L /\
     (step_n_in_L_relaxed pcf stepf s n L s'))
`;

val step_n_in_L_thm = save_thm("step_n_in_L_thm",
  REWRITE_RULE [step_n_in_L_relaxed_def] step_n_in_L_def
);

val step_n_in_L_onlyL_thm = store_thm(
   "step_n_in_L_onlyL_thm", ``
!pcf stepf.
!s n L s'.
(step_n_in_L pcf stepf s n L s') ==>
(
  (* ((pcf s) IN L) /\ *)
  (!n' s''. n' < n ==> step_n stepf s n' s'' ==> pcf(s'') IN L)
)
``,
  SIMP_TAC std_ss [step_n_in_L_thm] >>
  REPEAT STRIP_TAC >>
  Cases_on `n'` >- (
    FULL_SIMP_TAC std_ss [step_n_def, FUNPOW]
  ) >>
  `0 < SUC n''` by (SIMP_TAC arith_ss []) >>
  METIS_TAC [step_n_deterministic_thm]
);

val step_n_in_L_IMP_SUPER_thm = store_thm(
   "step_n_in_L_IMP_SUPER_thm", ``
!pcf stepf.
!s n L L' s'.
  (L SUBSET L') ==>
  (step_n_in_L pcf stepf s n L  s') ==>
  (step_n_in_L pcf stepf s n L' s')
``,
  REWRITE_TAC [step_n_in_L_thm, SUBSET_DEF] >>
  METIS_TAC []
);

val step_n_in_L_SEQ_thm = store_thm(
   "step_n_in_L_SEQ_thm", ``
!pcf stepf.
!s n_A L_A s' n_B L_B s''.
  (step_n_in_L pcf stepf s  n_A L_A s') ==>
  (step_n_in_L pcf stepf s' n_B L_B s'') ==>
  (step_n_in_L pcf stepf s (n_A + n_B) (L_A UNION L_B) s'')
``,
  REWRITE_TAC [step_n_in_L_thm, step_n_def] >>
  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC (arith_ss++pred_setSimps.PRED_SET_ss) []
  ) >> (
    REWRITE_TAC [Once ADD_SYM] >>
    ASM_SIMP_TAC (arith_ss++pred_setSimps.PRED_SET_ss) [step_n_def, FUNPOW_ADD]
  ) >>

  Cases_on `n' < n_A` >- (
    METIS_TAC []
  ) >>

  (* n' = n_A + some difference *)
  `?diff. n' = diff + n_A` by (
    METIS_TAC [LESS_EQ_EXISTS, NOT_LESS, ADD_SYM]
  ) >>

  (* that difference < n_B *)
  `diff < n_B` by (
    ASM_SIMP_TAC (arith_ss) []
  ) >>

  (* with that, just solve with assumptions and FUNPOW_ADD *)
  Cases_on `diff = 0` >> (
    FULL_SIMP_TAC (arith_ss) [FUNPOW_ADD, FUNPOW_0]
  )
);

val conc_step_n_in_L_relaxed_def = Define `
  conc_step_n_in_L_relaxed sr = step_n_in_L_relaxed symb_concst_pc sr.sr_step_conc
`;

val conc_step_n_in_L_def = Define `
  conc_step_n_in_L sr = step_n_in_L symb_concst_pc sr.sr_step_conc
`;

val conc_step_n_in_L_IMP_relaxed_thm = store_thm(
   "conc_step_n_in_L_IMP_relaxed_thm", ``
!sr.
!s n L s'.
(conc_step_n_in_L sr s n L s') ==>
(conc_step_n_in_L_relaxed sr s n L s')
``,
  METIS_TAC [conc_step_n_in_L_def, conc_step_n_in_L_relaxed_def, step_n_in_L_def]
);



(*
GOAL: MULTISTEP SOUNDNESS
=======================================================
*)
val symb_hl_step_in_L_sound_def = Define `
  symb_hl_step_in_L_sound sr (sys, L, Pi) =
    !s H.
    (symb_minimal_interpretation sr sys H) ==>
    (symb_matchstate sr sys H s) ==>
    (?n s'.
      (conc_step_n_in_L sr s n L s') /\
      (?sys'. sys' IN Pi /\ symb_matchstate_ext sr sys' H s')
    )
`;

(* TODO: for rules use DELETE (..) instead of DIFF {..} *)

(*
(*
WIP: SANITY: MULTISTEP SOUNDNESS IMPLIES INCLUSION OF ALL STARTING STATES IN REACHABLE STATE PATH CONDITIONS
=======================================================
*)
(* something similar could be proven for the transformations of Pi with the rules,
   i.e. path conditions in the reachable states as a whole can only get less restrictive and never more restrictive *)
(* no underapproximation *)
val symb_hl_step_in_L_sound_IMP_overapprox_thm = store_thm(
   "symb_hl_step_in_L_sound_IMP_overapprox_thm", ``
!sr.
!sys L Pi.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (!s H.
     (symb_interpr_symbpcond sr H sys) ==>
     (?sys'. sys' IN Pi /\ )
symb_interpr_ext H' H
  )
``,
  cheat
);
*)




(*
SUBSTITUTION OF SYMBOLIC EXPRESSIONS
=======================================================
*)
val symb_subst_store_def = Define `
    symb_subst_store sr subst store =
      (\var. OPTION_MAP (sr.sr_subst_f subst) (store var))
`;
val symb_subst_def = Define `
    symb_subst sr subst sys =
      (SymbSymbSt
        (symb_symbst_pc sys)
        (symb_subst_store sr subst (symb_symbst_store sys))
        (sr.sr_subst_f subst (symb_symbst_pcond sys))
        (symb_symbst_extra sys))
`;
val symb_subst_set_def = Define `
    symb_subst_set sr subst Pi =
      (IMAGE (symb_subst sr subst) Pi)
`;

val symb_subst_store_thm = store_thm(
   "symb_subst_store_thm", ``
!sr.
!subst store var.
  ((store var = NONE) ==> ((symb_subst_store sr subst store) var = NONE)) /\
  (!e. (store var = SOME e) ==> ((symb_subst_store sr subst store) var = SOME (sr.sr_subst_f subst e)))
``,
  METIS_TAC [symb_subst_store_def, optionTheory.OPTION_MAP_DEF]
);



val _ = export_theory();
