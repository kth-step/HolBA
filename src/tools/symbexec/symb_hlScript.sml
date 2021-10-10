open HolKernel Parse boolLib bossLib;

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
(* TODO: better rename type variables to alpha, beta, etc.
   because HOL4 seems to order them alphabetically for type parameters *)
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
val symb_symbst_pcond_def = Define `
  symb_symbst_pcond (SymbSymbSt _ _ pcond) = pcond
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

val _ = Datatype `symb_rec_t =
   <|
      sr_val_true        : 'val;

      sr_interpret_f     : (('symbol, 'val) symb_interpret_t) ->
                           'symbexpr ->
                           'val;

      sr_step_conc       : (('label, 'var, 'val) symb_concst_t) ->
                           (('label, 'var, 'val) symb_concst_t);

      sr_step_symb       : (('label, 'var, 'symbexpr) symb_symbst_t) ->
                           ((('label, 'var, 'symbexpr) symb_symbst_t) ->
                           bool);
   |>`;


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
  symb_interpr_symbstore sr H sys =
    (SymbConcSt
       (symb_symbst_pc sys)
       ((OPTION_MAP (sr.sr_interpret_f H)) o (symb_symbst_store sys)))
`;

val symb_interpr_symbpcond_def = Define `
  symb_interpr_symbpcond sr H sys =
    (sr.sr_interpret_f H (symb_symbst_pcond sys) = sr.sr_val_true)
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
     symb_interpr_symbstore sr H sys = s /\
     symb_interpr_symbpcond sr H sys)
`;

val symb_matchstate_ext_def = Define `
  symb_matchstate_ext sr sys H s =
    (?H'. symb_interpr_ext H' H /\
          symb_matchstate sr sys H' s)
`;

(*
GOAL: SINGLE STEP SOUNDNESS
=======================================================
*)
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

val step_n_in_L_def = Define `
  step_n_in_L pcf stepf s n L s' =
    (step_n stepf s n s' /\
     (pcf s) IN L /\
     (!n'. n' < n ==>
        ?s''. step_n stepf s n' s'' /\ pcf(s'') IN L))
`;

val step_n_in_L_onlyL_thm = store_thm("step_n_in_L_onlyL_thm", ``
!pcf stepf.
!s n L s'.
(step_n_in_L pcf stepf s n L s') ==>
(
  ((pcf s) IN L) /\
  (!n' s''. n' < n ==> step_n stepf s n' s'' ==> pcf(s'') IN L)
)
``,
  SIMP_TAC std_ss [step_n_in_L_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [step_n_deterministic_thm]
);

val conc_step_n_in_L_def = Define `
  conc_step_n_in_L sr = step_n_in_L symb_concst_pc sr.sr_step_conc
`;



(*
GOAL: MULTISTEP SOUNDNESS
=======================================================
*)
val symb_hl_step_in_L_sound_def = Define `
  symb_hl_step_in_L_sound sr (sys, L, Pi) =
    !s H. 
    (symb_matchstate sr sys H s) ==>
    (?n s'.
      (n > 0) /\
      (conc_step_n_in_L sr s n L s') /\
      (?sys'. sys' IN Pi /\ symb_matchstate_ext sr sys' H s')
    )
`;


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
  REWRITE_TAC [symb_step_sound_def, symb_matchstate_ext_def, symb_hl_step_in_L_sound_def, conc_step_n_in_L_def, step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  `?sys'. sys' IN Pi /\ symb_matchstate sr sys' H (sr.sr_step_conc s)` by (
    METIS_TAC []
  ) >>
  PAT_X_ASSUM ``!x y. z`` (K ALL_TAC) >>

  Q.EXISTS_TAC `SUC 0` >>
  Q.EXISTS_TAC `sr.sr_step_conc s` >>

  SIMP_TAC arith_ss [step_n_def, arithmeticTheory.FUNPOW] >>

  `symb_concst_pc s IN L` by (
    METIS_TAC [symb_matchstate_def]
  ) >>

  REPEAT STRIP_TAC >| [
    ASM_REWRITE_TAC []
  ,
    `n' = 0` by (
      ASM_SIMP_TAC arith_ss []
    ) >>
    ASM_REWRITE_TAC [arithmeticTheory.FUNPOW]
  ,
    METIS_TAC [symb_interpr_ext_id_thm]
  ]
);

val symb_rule_SEQ_thm = store_thm("symb_rule_SEQ_thm", ``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B Pi_C.
  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (Pi_C = (Pi_A DIFF {sys_B}) UNION Pi_B) ==>
  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, Pi_C))
``,
  cheat
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

(* TODO: proof compatibility with (this should imply) Didrik's contracts, see notes for that *)
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


val _ = export_theory();
