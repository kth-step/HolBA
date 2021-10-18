open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;
open combinTheory;

val _ = new_theory "symb_hl";

(*
``x:(('a, 'b, 'c, 'd) bir_symb_rec_t)``
``x:('c list)``

``x:(bir_symb_state_t)``

*)

(*
RECORD FOR REPRESENTING GENERIC CONCRETE AND SYMBOLIC TRANSITION SYSTEM
=======================================================
*)
val _ = Datatype `symb_concst_t =
   SymbConcSt 'a_label ('b_var -> 'c_val option)
`;
val symb_concst_pc_def = Define `
  symb_concst_pc (SymbConcSt lbl _) = lbl
`;
val symb_concst_store_def = Define `
  symb_concst_store (SymbConcSt _ store) = store
`;
(*
``SymbConcSt (0w:word64) (K (SOME "hallo"))``
*)

val _ = Datatype `symb_symbst_t =
   SymbSymbSt 'a_label ('b_var -> 'c_symbexpr option) 'c_symbexpr
`;
val symb_symbst_pc_def = Define `
  symb_symbst_pc (SymbSymbSt lbl _ _) = lbl
`;
val symb_symbst_store_def = Define `
  symb_symbst_store (SymbSymbSt _ store _) = store
`;
val symb_symbst_store_update_def = Define `
  symb_symbst_store_update var symbexpr (SymbSymbSt lbl store pcond) =
    SymbSymbSt lbl ((var =+ (SOME symbexpr)) store) pcond
`;
val symb_symbst_pcond_def = Define `
  symb_symbst_pcond (SymbSymbSt _ _ pcond) = pcond
`;
val symb_symbst_pcond_update_def = Define `
  symb_symbst_pcond_update pcond_f (SymbSymbSt lbl store pcond) =
    SymbSymbSt lbl store (pcond_f pcond)
`;

val _ = Datatype `symb_interpret_t =
   SymbInterpret ('a_symbol -> 'b_val option)
`;
val symb_interpr_ext_def = Define `
  symb_interpr_ext (SymbInterpret i1) (SymbInterpret i2) =
    (!symb. (i2 symb <> NONE) ==> (i1 symb = i2 symb))
`;

val symb_interpr_ext_id_thm = store_thm("symb_interpr_ext_id_thm", ``
!H. symb_interpr_ext H H
``,
  STRIP_TAC >>
  Cases_on `H` >>
  METIS_TAC [symb_interpr_ext_def]
);

val symb_interpr_ext_TRANS_thm = store_thm("symb_interpr_ext_TRANS_thm", ``
!H H' H''.
  (symb_interpr_ext H  H' ) ==>
  (symb_interpr_ext H' H'') ==>
  (symb_interpr_ext H  H'' )
``,
  REPEAT STRIP_TAC >>
  Cases_on `H` >> Cases_on `H'` >> Cases_on `H''` >>
  METIS_TAC [symb_interpr_ext_def]
);

val symb_interpr_ext_symb_NONE_thm = store_thm(
   "symb_interpr_ext_symb_NONE_thm", ``
!h symb.
symb_interpr_ext (SymbInterpret h) (SymbInterpret ((symb =+ NONE) h))
``,
  METIS_TAC [symb_interpr_ext_def, APPLY_UPDATE_THM]
);

val _ = Datatype `symb_rec_t =
   <|
      sr_val_true        : 'c_val;

      sr_interpret_f     : (('d_symbol, 'c_val) symb_interpret_t) ->
                           'e_symbexpr ->
                           'c_val option;

      sr_step_conc       : (('a_label, 'b_var, 'c_val) symb_concst_t) ->
                           (('a_label, 'b_var, 'c_val) symb_concst_t);

      sr_step_symb       : (('a_label, 'b_var, 'e_symbexpr) symb_symbst_t) ->
                           ((('a_label, 'b_var, 'e_symbexpr) symb_symbst_t) ->
                           bool);
   |>`;


val symb_list_of_types = [
  (*mk_thy_type {Tyop="symb_concst_t",   Thy="scratch", Args=[Type.alpha, Type.beta, Type.gamma]}*)
  mk_type ("symb_concst_t", [Type.alpha, Type.beta, Type.gamma])
];

val symb_TYPES_thms = (flatten (map type_rws symb_list_of_types));
val symb_TYPES_ss = rewrites symb_TYPES_thms;


(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
val _ = Datatype `bir_conc_state_t = int`;
val _ = Datatype `bir_symb_state_t = int`;

val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir a b c d =
    <|
      sr_val_true        := a;
      sr_interpret_f     := b;
      sr_step_conc       := c;
      sr_step_symb       := d;
   |>
`;
*)

(*
NOTATION: INTERPRETATION OF SYMBOLIC STATES AND SYMBOLIC PATH CONDITIONS
=======================================================
*)
val symb_interpr_symbstore_def = Define `
  symb_interpr_symbstore sr H sys s =
    (!var. (symb_symbst_store sys var <> NONE \/ symb_concst_store s var <> NONE) ==>
         ?symbexp v.
            symb_symbst_store sys var = SOME symbexp /\
            symb_concst_store s var = SOME v /\
            sr.sr_interpret_f H symbexp = SOME v)
`;

val symb_interpr_symbpcond_def = Define `
  symb_interpr_symbpcond sr H sys =
    (sr.sr_interpret_f H (symb_symbst_pcond sys) = SOME sr.sr_val_true)
`;

(*
NOTATION: STATE MATCHING
=======================================================
*)
(*
(syl,syst,syp)
(l, st)
*)
val symb_matchstate_def = Define `
  symb_matchstate sr sys H s =
    (symb_symbst_pc sys = symb_concst_pc s /\
     symb_interpr_symbstore sr H sys s /\
     symb_interpr_symbpcond sr H sys)
`;

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
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss)
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
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [] >>

  REPEAT STRIP_TAC >- (
    (* first take care of the pc *)
    FULL_SIMP_TAC (std_ss++symb_TYPES_ss)
      [symb_matchstate_def, symb_concst_pc_def, symb_symbst_pc_def]
  ) >>

  (* and now the concrete store *)
  METIS_TAC [symb_concst_store_def, symb_matchstate_UNIQUE_store_thm]
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



(*
NOTATION: MULTISTEP WITH LABEL SET
=======================================================
*)

(* n steps deterministic transition relation with using FUNPOW *)
val step_n_def = Define `
  (step_n stepf s n s' = (FUNPOW stepf n s = s'))
`;

val step_n_deterministic_thm = store_thm("step_n_deterministic_thm", ``
!stepf.
!s n s' s''.
(step_n stepf s n s') ==>
(step_n stepf s n s'') ==>
(s' = s'')
``,
  SIMP_TAC std_ss [step_n_def]
);
val step_n_total_thm = store_thm("step_n_total_thm", ``
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

val step_n_in_L_onlyL_thm = store_thm("step_n_in_L_onlyL_thm", ``
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

val step_n_in_L_IMP_SUPER_thm = store_thm("step_n_in_L_IMP_SUPER_thm", ``
!pcf stepf.
!s n L L' s'.
  (L SUBSET L') ==>
  (step_n_in_L pcf stepf s n L  s') ==>
  (step_n_in_L pcf stepf s n L' s')
``,
  REWRITE_TAC [step_n_in_L_thm, SUBSET_DEF] >>
  METIS_TAC []
);

val step_n_in_L_SEQ_thm = store_thm("step_n_in_L_SEQ_thm", ``
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

val conc_step_n_in_L_IMP_relaxed_thm = store_thm("conc_step_n_in_L_IMP_relaxed_thm", ``
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
    (symb_matchstate sr sys H s) ==>
    (?n s'.
      (conc_step_n_in_L sr s n L s') /\
      (?sys'. sys' IN Pi /\ symb_matchstate_ext sr sys' H s')
    )
`;

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
GOAL: INFERENCE RULES
=======================================================
*)
val symb_rule_STEP_thm = store_thm("symb_rule_STEP_thm", ``
!sr.
!sys L Pi.
  (symb_step_sound sr) ==>
  (sr.sr_step_symb sys = Pi) ==>
  ((symb_symbst_pc sys) IN L) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_step_sound_def, symb_matchstate_ext_def, symb_hl_step_in_L_sound_def, conc_step_n_in_L_def, step_n_in_L_thm] >>
  REPEAT STRIP_TAC >>

  `?sys'. sys' IN Pi /\ symb_matchstate sr sys' H (sr.sr_step_conc s)` by (
    METIS_TAC []
  ) >>
  PAT_X_ASSUM ``!x y. z`` (K ALL_TAC) >>

  Q.EXISTS_TAC `SUC 0` >>
  Q.EXISTS_TAC `sr.sr_step_conc s` >>

  SIMP_TAC arith_ss [step_n_def, FUNPOW] >>

  `symb_concst_pc s IN L` by (
    METIS_TAC [symb_matchstate_def]
  ) >>

  REPEAT STRIP_TAC >| [
    ASM_REWRITE_TAC []
  ,
    METIS_TAC [symb_interpr_ext_id_thm]
  ]
);

val symb_rule_SEQ_thm = store_thm("symb_rule_SEQ_thm", ``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B.
  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (symb_hl_step_in_L_sound sr (sys_B, L_B, Pi_B)) ==>
  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, (Pi_A DIFF {sys_B}) UNION Pi_B))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def, conc_step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_matchstate sr sys_A H s ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* the case when after A we actually execute through sys_B *)
  Cases_on `sys' = sys_B` >- (
    (* execute from s' (sys') with fragment B *)
    PAT_X_ASSUM ``!s H. symb_matchstate sr sys_B H s ==> A`` (ASSUME_TAC o (Q.SPECL [`s'`, `H'`])) >>
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

    METIS_TAC [symb_interpr_ext_TRANS_thm]
  ) >>

  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC [step_n_in_L_IMP_SUPER_thm, SUBSET_UNION]
);

val symb_rule_INF_thm = store_thm("symb_rule_INF_thm", ``
!sr.
!sys L Pi sys'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (!H. ~(symb_interpr_symbpcond sr H sys')) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi DIFF {sys'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_matchstate sr sys H s ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_matchstate_ext_def] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `sys' = sys''` >> (
    METIS_TAC []
  )
);

val symb_pcondwiden_def = Define `
  symb_pcondwiden sr sys sys' = (
    (symb_symbst_pc sys =
     symb_symbst_pc sys') /\
    (symb_symbst_store sys =
     symb_symbst_store sys') /\
    (!H.
     (symb_interpr_symbpcond sr H sys) ==>
     (symb_interpr_symbpcond sr H sys'))
  )
`;

val symb_rule_CONS_S_thm = store_thm("symb_rule_CONS_S_thm", ``
!sr.
!sys' sys L Pi.
  (symb_hl_step_in_L_sound sr (sys', L, Pi)) ==>
  (symb_pcondwiden sr sys sys') ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  `symb_matchstate sr sys' H s` by (
    Cases_on `sys` >> Cases_on `sys'` >>
    FULL_SIMP_TAC std_ss [symb_pcondwiden_def, symb_matchstate_def, symb_symbst_store_def, symb_interpr_symbstore_def] >>
    METIS_TAC []
  ) >>
  METIS_TAC []
);

val symb_rule_CONS_E_thm = store_thm("symb_rule_CONS_E_thm", ``
!sr.
!sys L Pi sys2 sys2'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_matchstate sr sys H s ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_matchstate_ext_def] >>

  (* the case when we would execute to sys2 *)
  Cases_on `sys' = sys2` >- (
    Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    Q.EXISTS_TAC `sys2'` >>
    ASM_SIMP_TAC std_ss [] >>
    Q.EXISTS_TAC `H'` >>

    FULL_SIMP_TAC std_ss [symb_pcondwiden_def, symb_matchstate_def, symb_symbst_store_def, symb_interpr_symbstore_def] >>
    METIS_TAC []
  ) >>

  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC []
);

val symb_rule_CONS_thm = store_thm("symb_rule_CONS_thm", ``
!sr.
!sys1' sys1 L Pi sys2 sys2'.
  (symb_hl_step_in_L_sound sr (sys1', L, Pi)) ==>
  (symb_pcondwiden sr sys1 sys1') ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys1, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_CONS_S_thm, symb_rule_CONS_E_thm]
);

(* construct symbolic expression with semantics of
     conjuncting an expression with an equality of two other expressions
   e.g.: e1 = (v), e2 = (5), conj1 = (x > 10)
     then: (v) = (5) /\ (x > 10) *)
val symb_is_expr_conj_eq_def = Define `
  symb_is_expr_conj_eq sr expr_conj_eq =
    (!e1 e2 conj1. !H.
       (sr.sr_interpret_f H (expr_conj_eq e1 e2 conj1) = SOME sr.sr_val_true) =
       ((sr.sr_interpret_f H conj1 = SOME sr.sr_val_true) /\
        (?v. sr.sr_interpret_f H e1 = SOME v /\
             sr.sr_interpret_f H e2 = SOME v)))
`;

(* predicate for functions that make expressions that represent exactly a symbol *)
val symb_is_mk_symbexpr_symbol_def = Define `
  symb_is_mk_symbexpr_symbol sr mk_symbexpr =
    (!h symb v.
       (h symb = SOME v) ==>
       (sr.sr_interpret_f (SymbInterpret h) (mk_symbexpr symb) = SOME v))
`;

(* predicate for independent symbols in symbolic expressions and symbolic states *)
val symb_is_independent_symbol_symbexp_def = Define `
  symb_is_independent_symbol_symbexp sr symbexp symb =
    (!h val_o.
       sr.sr_interpret_f (SymbInterpret h) symbexp =
       sr.sr_interpret_f (SymbInterpret ((symb =+ val_o) h)) symbexp)
`;
val symb_is_independent_symbol_store_def = Define `
  symb_is_independent_symbol_store sr store symb = 
    (!var. store var <> NONE ==>
        ?symbexp. store var = SOME symbexp /\
                  symb_is_independent_symbol_symbexp sr symbexp symb)
`;
val symb_is_independent_symbol_def = Define `
  symb_is_independent_symbol sr sys symb =
    (symb_is_independent_symbol_store sr (symb_symbst_store sys) symb /\
     symb_is_independent_symbol_symbexp sr (symb_symbst_pcond sys) symb)
`;

(*
val symb_is_independent_symbol_IMP_symb_matchstate_thm = store_thm(
   "symb_is_independent_symbol_IMP_symb_matchstate_thm", ``
!sr.
!sys s h symb.
  (symb_is_independent_symbol sr sys symb) ==>

  (symb_matchstate sr sys (SymbInterpret h) s =
   symb_matchstate sr sys (SymbInterpret ((symb =+ NONE) h)) s)
``,
  cheat
);

val symb_is_independent_symbol_IMP_freshsymb_thm = store_thm(
   "symb_is_independent_symbol_IMP_freshsymb_thm", ``
!sr expr_conj_eq mk_symbexpr.
(symb_is_expr_conj_eq sr expr_conj_eq) ==>
(symb_is_mk_symbexpr_symbol sr mk_symbexpr) ==>

(!sys sys' var symbexp symb H s.
  (symb_is_independent_symbol sr sys symb) ==>
  (symb_symbst_store sys var = SOME symbexp) ==>
  (sys' = symb_symbst_pcond_update
             (expr_conj_eq (mk_symbexpr symb) symbexp)
             (symb_symbst_store_update var (mk_symbexpr symb) sys)
  ) ==>
  (symb_matchstate_ext sr sys  H s =
   symb_matchstate_ext sr sys' H s)
)
``,
  cheat
);

(* rule to introduce fresh symbols as values of store variables
     (as abbreviations or as first step of forgetting values) *)
val symb_rule_FRESH_thm = store_thm("symb_rule_FRESH_thm", ``
!sr expr_conj_eq mk_symbexpr.
(symb_is_expr_conj_eq sr expr_conj_eq) ==>
(symb_is_mk_symbexpr_symbol sr mk_symbexpr) ==>

(!sys L Pi sys2 sys2' var symbexp symb.
  (symb_is_independent_symbol sr sys symb) ==>
  (symb_is_independent_symbol sr sys2 symb) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (sys2' = symb_symbst_pcond_update
             (expr_conj_eq (mk_symbexpr symb) symbexp)
             (symb_symbst_store_update var (mk_symbexpr symb) sys2)
  ) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
)
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  (* select H where symbol is not mapped *)
  Cases_on `H` >> Q.RENAME1_TAC `SymbInterpret h` >>
  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`s`, `SymbInterpret ((symb =+ NONE) h)`])) >>

  `symb_matchstate sr sys (SymbInterpret ((symb =+ NONE) h)) s` by (
    METIS_TAC [symb_is_independent_symbol_IMP_symb_matchstate_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  (* the case when we would execute to sys2 *)
  Cases_on `sys' = sys2` >- (
    Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    METIS_TAC [symb_simplification_symb_matchstate_ext_thm]

symb_is_independent_symbol_IMP_symb_matchstate_thm
symb_is_independent_symbol_IMP_freshsymb_thm
  ) >>

  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC [symb_matchstate_ext_w_ext_thm, symb_interpr_ext_symb_NONE_thm]
symb_matchstate_ext_w_ext_thm
symb_interpr_ext_symb_NONE_thm
);
*)

val symb_simplification_def = Define `
  symb_simplification sr sys symbexp symbexp' =
    (!H.
     (symb_interpr_symbpcond sr H sys) ==>
     (sr.sr_interpret_f H symbexp = sr.sr_interpret_f H symbexp'))
`;

val symb_simplification_symb_matchstate_ext_thm = store_thm(
   "symb_simplification_symb_matchstate_ext_thm", ``
!sr.
!sys var symbexp symbexp' H s.
  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_simplification sr sys symbexp symbexp') ==>

  (symb_matchstate_ext sr sys H s =
   symb_matchstate_ext sr (symb_symbst_store_update var symbexp' sys) H s)
``,
  REPEAT STRIP_TAC >>
(*
  HO_MATCH_MP_TAC EQ_EXT >> STRIP_TAC >>
  HO_MATCH_MP_TAC EQ_EXT >> STRIP_TAC >>
*)

  FULL_SIMP_TAC std_ss [symb_simplification_def, symb_matchstate_def, symb_matchstate_ext_def] >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `H'` >>
    Cases_on `sys` >> Cases_on `s` >>

    FULL_SIMP_TAC std_ss
      [symb_concst_pc_def, symb_symbst_pc_def, symb_symbst_pcond_def,
       symb_symbst_store_update_def, symb_interpr_symbpcond_def] >>

    PAT_X_ASSUM ``!H. A`` (ASSUME_TAC o (Q.SPEC `H'`)) >>
    REV_FULL_SIMP_TAC std_ss [symb_symbst_store_def]
  ) >> (
    (* still have to prove that the store matches *)
    FULL_SIMP_TAC std_ss
      [symb_interpr_symbstore_def, symb_concst_store_def,
       symb_symbst_store_def, APPLY_UPDATE_THM] >>
    REPEAT STRIP_TAC
  ) >> (
    (* for the updated variable, and for all others *)
    Cases_on `var = var'` >> (
      FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def, symb_concst_store_def, symb_symbst_store_def] >>

      PAT_X_ASSUM ``!H. A`` (ASSUME_TAC o (Q.SPEC `var'`)) >>
      REV_FULL_SIMP_TAC std_ss []
    )
  )
);

val symb_rule_SUBST_thm = store_thm("symb_rule_SUBST_thm", ``
!sr.
!sys L Pi sys2 sys2' var symbexp symbexp'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr sys2 symbexp symbexp') ==>
  (sys2' = symb_symbst_store_update var symbexp' sys2) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_matchstate sr sys H s ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* the case when we would execute to sys2 *)
  Cases_on `sys' = sys2` >- (
    Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    METIS_TAC [symb_simplification_symb_matchstate_ext_thm]
  ) >>

  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  METIS_TAC []
);



(*
NOTATION: DEFINE PROPERTY TRANSFER ASSUMPTIONS AND GOAL
=======================================================
*)
val P_entails_an_interpret_def = Define `
  P_entails_an_interpret sr P sys =
    (!s.
     (symb_concst_pc s = symb_symbst_pc sys) ==>
     (P s) ==>
     (?H. symb_matchstate sr sys H s))
`;

val Pi_overapprox_Q_def = Define `
  Pi_overapprox_Q sr P sys Pi Q =
    (!sys' s s' H.
     (sys' IN Pi) ==>
     (P s) ==>
     (symb_matchstate sr sys H s) ==>
     (symb_matchstate_ext sr sys' H s') ==>
     (Q s s'))
`;

val prop_holds_def = Define `
  prop_holds sr l L P Q =
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
val symb_prop_transfer_thm = store_thm("symb_prop_transfer_thm", ``
!sr sys L Pi P Q.
  (P_entails_an_interpret sr P sys) ==>
  (Pi_overapprox_Q sr P sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds sr (symb_symbst_pc sys) L P Q)
``,
  REWRITE_TAC [P_entails_an_interpret_def, Pi_overapprox_Q_def, prop_holds_def, symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
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

val symb_prop_transfer_binHoare_thm = store_thm("symb_prop_transfer_binHoare_thm", ``
!sr.
!Q' l L P Q.
  (Q' = \s. \s'. Q s' /\ (~((symb_concst_pc s') IN (COMPL L)))) ==>
  (prop_holds sr l (COMPL L) P Q') ==>
  (abstract_jgmt (symb_hl_etl_wm sr) l L P Q)
``,
  REWRITE_TAC [prop_holds_def, abstract_jgmt_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `ms`)) >>

  REV_FULL_SIMP_TAC (std_ss++bir_wm_SS) [symb_hl_etl_wm_def, symb_hl_weak_def] >>

  METIS_TAC [conc_step_n_in_L_IMP_relaxed_thm]
);

(* should go to BIR auxTheory *)
val FUNPOW_OPT_SOME_thm = store_thm("FUNPOW_OPT_SOME_thm", ``
!f g.
   (!y. f y = SOME (g y)) ==>
   (!n x.
      (FUNPOW_OPT f n x = SOME (FUNPOW g n x)))
``,
  GEN_TAC >> GEN_TAC >> STRIP_TAC >>
  Induct_on `n` >- (
    REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW]
  ) >>
  REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW] >>
  ASM_SIMP_TAC std_ss [GSYM bir_auxiliaryTheory.FUNPOW_OPT_def]
);


val symb_hl_trs_thm = store_thm("symb_hl_trs_thm",
  ``!sr. !x. (symb_hl_trs sr x) = SOME (sr.sr_step_conc x)``,
  METIS_TAC [symb_hl_trs_def]
);

val FUNPOW_OPT_SOME_symb_hl_trs_thm = store_thm("FUNPOW_OPT_SOME_symb_hl_trs_thm",
  ``!sr. !n x.
      (FUNPOW_OPT (symb_hl_trs sr) n x = SOME (FUNPOW sr.sr_step_conc n x))``,
  METIS_TAC [FUNPOW_OPT_SOME_thm, symb_hl_trs_thm]
);


val symb_hl_is_weak = store_thm("symb_hl_is_weak",
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
