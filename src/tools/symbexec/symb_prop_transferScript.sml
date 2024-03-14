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
Definition P_entails_an_interpret_def:
  P_entails_an_interpret sr P sys =
    (!s.
     (symb_concst_pc s = symb_symbst_pc sys) ==>
     (P s) ==>
     (?H. symb_matchstate sr sys H s))
End

Definition Pi_overapprox_Q_def:
  Pi_overapprox_Q sr P sys Pi Q =
    (!sys' s s' H.
     (sys' IN Pi) ==>
     (P s) ==>
     (symb_matchstate sr sys H s) ==>
     (symb_matchstate_ext sr sys' H s') ==>
     (Q s s'))
End

Definition prop_holds_def:
  prop_holds sr l L P Q =
    (!s.
     (symb_concst_pc s = l) ==>
     (P s) ==>
     (?n s'.
       conc_step_n_in_L sr s n L s' /\
       Q s s'))
End


(*
GOAL: PROPERTY TRANSFER THEOREM
=======================================================
*)
Theorem symb_prop_transfer_thm:
  !sr.
!sys L Pi P Q.
  (symb_symbols_f_sound sr) ==>
  (P_entails_an_interpret sr P sys) ==>
  (Pi_overapprox_Q sr P sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds sr (symb_symbst_pc sys) L P Q)
Proof
REWRITE_TAC [P_entails_an_interpret_def, Pi_overapprox_Q_def, prop_holds_def, symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [symb_matchstate_TO_minimal_thm]
QED

(*
GOAL: NOW CONSIDERING STORE TYPING INDIVIDUALLY
=======================================================
*)
Definition symb_concst_store_ty_sat_def:
  symb_concst_store_ty_sat sr sty s =
    (!vn.
       ((IS_SOME (sty vn)) \/ (IS_SOME ((symb_concst_store s) vn))) ==>
       (?ty v.
          (sty vn = SOME ty) /\
          ((symb_concst_store s) vn = SOME v) /\
          (sr.sr_typeof_val v = ty)))
End
(* notice the special case: sys with type errors in a symbolic expression! *)
Definition symb_symbst_store_ty_def:
  symb_symbst_store_ty sr sys =
    (\vn. OPTION_BIND ((symb_symbst_store sys) vn) (sr.sr_typeof_exp))
End
Definition prop_holds_sty_def:
  prop_holds_sty sr l L sty P Q =
    (!s.
     (symb_concst_pc s = l) ==>
     (symb_concst_store_ty_sat sr sty s) ==>
     (P s) ==>
     (?n s'.
       conc_step_n_in_L sr s n L s' /\
       Q s s'))
End

Theorem prop_holds_sty_thm:
  !sr l L sty P Q.
  (!s. P s ==> symb_concst_store_ty_sat sr sty s) ==>
  ((prop_holds_sty sr l L sty P Q) =
   (prop_holds sr l L P Q))
Proof
REWRITE_TAC [prop_holds_def, prop_holds_sty_def] >>
  METIS_TAC []
QED
Theorem prop_holds_sty_thm2:
  !sr l L sty P Q.
  ((prop_holds_sty sr l L sty P Q) =
   (prop_holds sr l L (\s. symb_concst_store_ty_sat sr sty s /\ P s) Q))
Proof
REWRITE_TAC [prop_holds_def, prop_holds_sty_def] >>
  METIS_TAC []
QED

Theorem symb_prop_transfer_sty_thm:
  !sr.
!sys L Pi P Q.
  (symb_symbols_f_sound sr) ==>
  (P_entails_an_interpret sr (\s. symb_concst_store_ty_sat sr (symb_symbst_store_ty sr sys) s /\ P s) sys) ==>
  (Pi_overapprox_Q sr (\s. symb_concst_store_ty_sat sr (symb_symbst_store_ty sr sys) s /\ P s) sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds_sty sr (symb_symbst_pc sys) L (symb_symbst_store_ty sr sys) P Q)
Proof
REWRITE_TAC [prop_holds_sty_thm2, symb_prop_transfer_thm]
QED



(*
GOAL: GENERIC INITIAL SYMBOLIC STATES (STORES, BUT ALSO PATH CONDITION AND "OTHER")
=======================================================
*)
(* deal with the special case: sys with type errors in a symbolic expression *)
Definition symb_symbst_store_notyerr_def:
  symb_symbst_store_notyerr sr sys =
    (!vn sv.
       ((symb_symbst_store sys) vn = SOME sv) ==>
       (IS_SOME (sr.sr_typeof_exp sv)))
End

Definition symb_symbst_is_GEN_def:
  symb_symbst_is_GEN sr sys =
    (?vn2sy vnS syS.
      (BIJ vn2sy vnS syS) /\
      (!vn. (~(vn IN vnS)) ==> ((symb_symbst_store sys) vn = NONE)) /\
      (!vn. vn IN vnS ==> ((symb_symbst_store sys) vn = SOME (sr.sr_mk_exp_symb_f(vn2sy vn))))
    )
End
(* is_GEN should imply notyerr... *)

Definition P_GEN_def:
  P_GEN sr sys P s =
      (symb_concst_store_ty_sat sr (symb_symbst_store_ty sr sys) s /\
       symb_concst_extra s = symb_symbst_extra sys /\
       P s)
End

(*
Theorem P_entails_an_interpret_GEN_thm:
  !sr P sys.
  (symb_mk_exp_symb_f_sound sr) ==>
  (* possibly also need symb_typeof_exp_sound_def *)
  (!H. sr.sr_interpret_f H (symb_symbst_pcond sys) = SOME sr.sr_val_true) ==>
  (symb_symbst_store_notyerr sr sys) ==>
  (symb_symbst_is_GEN sr sys) ==>
  (P_entails_an_interpret sr (P_GEN sr sys P) sys)
Proof
REWRITE_TAC [symb_symbst_store_notyerr_def, symb_symbst_is_GEN_def] >>
  FULL_SIMP_TAC std_ss [symb_record_soundTheory.symb_mk_exp_symb_f_sound_def, P_entails_an_interpret_def] >>
  REPEAT STRIP_TAC >>

  IMP_RES_TAC BIJ_INV >>
  rename1 `BIJ sy2vn syS vnS` >>

  Q.EXISTS_TAC `SymbInterpret (\sy. if sy IN syS then (symb_concst_store s) (sy2vn sy) else NONE)` >>

  cheat
QED
*)


(*
GOAL: PROPERTY TRANSFER COMPATIBILITY (BINARY HOARE LOGIC)
=======================================================
*)
local
  open total_program_logicTheory;
  open transition_systemTheory;
  open program_logicSimps;
in

(*
  it seems we can in principle produce contracts of all code fragments
  - unless the start label is in the end label set, because in this case the transition system could not "start"
  - unless it cannot be exhaustively symbolically executed, like if they contain unbound loops, or impractically largely bound loops
*)

Definition symb_hl_trs_def:
  symb_hl_trs sr st = SOME (sr.sr_step_conc st)
End

Definition symb_hl_weak_def:
  symb_hl_weak sr ls st st' =
    (?n. (conc_step_n_in_L_relaxed sr st n (COMPL ls) st' /\ (~((symb_concst_pc st') IN (COMPL ls)))))
End

Definition symb_hl_etl_wm_def:
  symb_hl_etl_wm sr = <|
    trs  := symb_hl_trs sr;
    weak := symb_hl_weak sr;
    ctrl := symb_concst_pc
  |>
End

Theorem symb_prop_transfer_binHoare_thm:
  !sr.
!Q' l L P Q.
  (Q' = \s. \s'. Q s' /\ (~((symb_concst_pc s') IN (COMPL L)))) ==>
  (prop_holds sr l (COMPL L) P Q') ==>
  (t_jgmt (symb_hl_etl_wm sr) l L P Q)
Proof
REWRITE_TAC [prop_holds_def, t_jgmt_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `s`)) >>

  REV_FULL_SIMP_TAC (std_ss++bir_wm_SS) [symb_hl_etl_wm_def, symb_hl_weak_def] >>

  METIS_TAC [conc_step_n_in_L_IMP_relaxed_thm]
QED

Theorem symb_hl_trs_thm:
  !sr. !x. (symb_hl_trs sr x) = SOME (sr.sr_step_conc x)
Proof
METIS_TAC [symb_hl_trs_def]
QED

Theorem FUNPOW_OPT_SOME_symb_hl_trs_thm:
  !sr. !n x.
      (FUNPOW_OPT (symb_hl_trs sr) n x = SOME (FUNPOW sr.sr_step_conc n x))
Proof
METIS_TAC [FUNPOW_OPT_SOME_thm, symb_hl_trs_thm]
QED


Theorem symb_hl_is_weak:
  !sr.
      first_enc (symb_hl_etl_wm sr)
Proof
SIMP_TAC (std_ss++bir_wm_SS) [first_enc_def, symb_hl_etl_wm_def, symb_hl_weak_def, symb_hl_trs_def] >>

  REWRITE_TAC [conc_step_n_in_L_relaxed_def, step_n_in_L_relaxed_def, step_n_in_L_thm, step_n_def, FUNPOW_OPT_SOME_symb_hl_trs_thm] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `n` >>

    (*`n > 0` by () >>*)
    FULL_SIMP_TAC std_ss [IN_COMPL, GREATER_DEF]
  )
QED

end;

val _ = export_theory();
