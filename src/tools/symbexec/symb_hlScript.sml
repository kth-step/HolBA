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
val _ = Datatype `symb_rec_t =
   <|
      sr_interpr_sypcond : 'h -> 'symbpcond -> bool;
      sr_interpr_systate : 'h -> 'symbst -> 'concst;
      sr_interpr_ext     : 'h -> 'h -> bool;
      sr_pc_conc         : 'concst -> 'label;
      sr_pc_symb         : 'symbst -> 'label;
      sr_pcond_symb      : 'symbst -> 'symbpcond;
      sr_step_conc       : 'concst -> 'concst;
      sr_step_symb       : 'symbst -> ('symbst -> bool);
   |>`;


(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
val _ = Datatype `bir_conc_state_t = int`;
val _ = Datatype `bir_symb_state_t = int`;

val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir a b c d e f g h =
    <|
      sr_interpr_sypcond := a;
      sr_interpr_systate := b;
      sr_interpr_ext     := c;
      sr_pc_conc         := d;
      sr_pc_symb         := e;
      sr_pcond_symb      := f;
      sr_step_conc       := g;
      sr_step_symb       := h;
   |>
`;
*)

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
    (sr.sr_interpr_systate H sys = s /\
     sr.sr_interpr_sypcond H (sr.sr_pcond_symb sys) /\
     sr.sr_pc_symb sys = sr.sr_pc_conc s)
`;

val symb_matchstate_ext_def = Define `
  symb_matchstate_ext sr sys H s =
    (?H'. sr.sr_interpr_ext H' H /\
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
       (!sys'. sys' IN Pi /\ symb_matchstate sr sys' H s')
     )
    )
`;



(*
NOTATION: MULTISTEP WITH LABEL SET
=======================================================
*)

(* maybe standardize with using POW *)
val step_n_def = Define `
  (step_n stepf s 0 s' = F) /\
  (step_n stepf s (SUC 0) s' = (stepf s = s')) /\
  (step_n stepf s (SUC n) s' = step_n stepf (stepf s) n s')
`;

(* proof step_n is deterministic step_n s n s' /\ step_n s n s'' ==> s
 = s'' *)
(* total: !s n > 0. ?s' *)

val step_n_in_L_def = Define `
  step_n_in_L pcf stepf s n L s' =
    (step_n stepf s n s' /\
     (pcf s) IN L /\
     (!n'. n' < n ==>
        ?s''. step_n stepf s n' s'' /\ pcf(s'') IN L))
`;

(* step_n_in_l ... ==> (() IN L /\ (!n' < n. !s''. step_n_in_l ==> pcf(s'') IN L)) *)

val conc_step_n_in_L_def = Define `
  conc_step_n_in_L sr = step_n_in_L sr.sr_pc_conc sr.sr_step_conc
`;



(*
GOAL: MULTISTEP SOUNDNESS
=======================================================
*)
val symb_hl_step_n_sound_def = Define `
  symb_hl_step_in_L_sound sr (sys, L, Pi) =
    !s H. 
    (symb_matchstate sr sys H s) ==>
    (?n s'.
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
  ((sr.sr_pc_symb sys) IN L) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  cheat
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
     (sr.sr_pc_conc s = sr.sr_pc_symb sys) ==>
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

(* TODO: see compatibility with (this should imply) Didrik's contracts *)
val prop_holds_def = Define `
  prop_holds sr l L P Q =
    (!s.
     (sr.sr_pc_conc s = l) ==>
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
!sr (sys, L, Pi) P Q.
  (P_entails_an_interpret sr P sys) ==>
  (Pi_overapprox_Q sr P sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds sr (sr.sr_pc_symb sys) L P Q)
``,
  cheat
);


val _ = export_theory();
