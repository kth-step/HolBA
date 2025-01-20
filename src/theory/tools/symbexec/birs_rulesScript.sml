open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open symb_interpretTheory;
open symb_recordTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;
open bir_symb_simpTheory;

open symb_typesLib;
open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "birs_rules";

val IMAGE_DIFF_ASSOC_thm = prove(``
!f s1 s2.
  (!x y. f x = f y <=> x = y) ==>
  ((IMAGE f s1) DIFF (IMAGE f s2) =
   IMAGE f (s1 DIFF s2))
``,
    fs [IMAGE_DEF, DIFF_DEF, EXTENSION] >>
    REPEAT STRIP_TAC >>
    EQ_TAC >> (
      METIS_TAC []
    )
);

val IMAGE_UNION_ASSOC_thm = prove(``
!f s1 s2.
  (!x y. f x = f y <=> x = y) ==>
  ((IMAGE f s1) UNION (IMAGE f s2) =
   IMAGE f (s1 UNION s2))
``,
    fs [IMAGE_DEF, UNION_DEF, EXTENSION] >>
    REPEAT STRIP_TAC >>
    EQ_TAC >> (
      METIS_TAC []
    )
);

val bestTheorem = prove(“
 !A B C.
  IMAGE birs_symb_to_symbst A DIFF {birs_symb_to_symbst B} UNION IMAGE birs_symb_to_symbst C =
  IMAGE birs_symb_to_symbst (A DIFF {B} UNION C)
”,
  REWRITE_TAC [GSYM IMAGE_SING] >>
  REWRITE_TAC
    [MATCH_MP IMAGE_DIFF_ASSOC_thm birs_symb_to_symbst_EQ_thm,
     MATCH_MP IMAGE_UNION_ASSOC_thm birs_symb_to_symbst_EQ_thm]
);


Theorem INSERT_SING_DIFF_ALT_thm[local]:
  !A B C.
     ((A INSERT C) DIFF {A}) UNION {B} = B INSERT (C DELETE A)
Proof
    fs [] >>
    METIS_TAC [INSERT_SING_UNION, UNION_COMM, DELETE_DEF]
QED


Definition birs_pcondinf_def:
  birs_pcondinf pcond =
  (!H.
    (birs_interpr_welltyped H) ==>
    (symb_interpr_for_symbs (bir_vars_of_exp pcond) H) ==>
    (birs_interpret_fun H pcond = SOME bir_val_false)
  )
End

Theorem birs_pcondinf_thm:
  !bprog pcond.
  birs_pcondinf pcond ==>
  symb_pcondinf (bir_symb_rec_sbir bprog) pcond
Proof
REWRITE_TAC [symb_rulesTheory.symb_pcondinf_def, birs_pcondinf_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def, symb_interpr_symbpcond_def, bir_bool_expTheory.bir_val_TF_dist]
QED

Definition birs_pcondwiden_def:
  birs_pcondwiden pcond pcond' =
    (!H.
      (birs_interpr_welltyped H) ==>
      (symb_interpr_for_symbs ((bir_vars_of_exp pcond) UNION (bir_vars_of_exp pcond')) H) ==>
      (birs_interpret_fun H pcond = SOME bir_val_true) ==>
      (birs_interpret_fun H pcond' = SOME bir_val_true))
End

Theorem birs_pcondwiden_thm:
  !bprog pcond pcond'.
  symb_pcondwiden (bir_symb_rec_sbir bprog) pcond pcond' <=>
  birs_pcondwiden pcond pcond'
Proof
REWRITE_TAC [symb_rulesTheory.symb_pcondwiden_def, birs_pcondwiden_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def, symb_interpr_symbpcond_def, bir_bool_expTheory.bir_val_TF_dist]
QED

(* ******************************************************* *)
(*      sound execution structure for SBIR                 *)
(* ******************************************************* *)
Definition birs_symb_exec_def:
  birs_symb_exec p (bs, L, bP) =
      (symb_hl_step_in_L_sound (bir_symb_rec_sbir p) (birs_symb_to_symbst bs, L, IMAGE birs_symb_to_symbst bP))
End

Theorem birs_symb_exec_SUBSET_thm:
  !p bs L Pi Pi'.
    (birs_symb_exec p (bs, L, Pi)) ==>
    (Pi SUBSET Pi') ==>
    (birs_symb_exec p (bs, L, Pi'))
Proof
  fs [birs_symb_exec_def] >>
  metis_tac [IMAGE_SUBSET, symb_recordTheory.symb_hl_step_in_L_sound_SUBSET_thm]
QED

Theorem birs_symb_exec_INSERT_DELETE_thm:
  !prog bs L A B C.
    birs_symb_exec prog (bs, L, A INSERT (B DELETE C)) ==>
    birs_symb_exec prog (bs, L, A INSERT B)
Proof
  rpt strip_tac >>
  ‘(A INSERT (B DELETE C)) SUBSET (A INSERT B)’ by (
    fs [INSERT_SUBSET, COMPONENT, SUBSET_INSERT_RIGHT, DELETE_SUBSET]
  ) >>
  metis_tac [birs_symb_exec_SUBSET_thm]
QED


(* ******************************************************* *)
(*      FREE SYMBS                                         *)
(* ******************************************************* *)
Definition birs_symb_symbols_set_def:
  birs_symb_symbols_set Pi =
      BIGUNION (IMAGE birs_symb_symbols Pi)
End

Theorem birs_symb_symbols_set_EQ_thm2:
  !prog Pi. symb_symbols_set (bir_symb_rec_sbir prog) (IMAGE birs_symb_to_symbst Pi) = birs_symb_symbols_set Pi
Proof
  REWRITE_TAC [birs_auxTheory.symb_symbols_set_ALT_thm, birs_symb_symbols_set_def] >>
  REWRITE_TAC [pred_setTheory.IMAGE_IMAGE, combinTheory.o_DEF, birs_symb_symbols_EQ_thm] >>
  METIS_TAC []
  (* birs_symb_symbols_set_EQ_thm *)
QED

Definition birs_freesymbs_def:
  birs_freesymbs bs sbs =
      ((birs_symb_symbols_set sbs) DIFF (birs_symb_symbols bs))
End

Theorem birs_freesymbs_thm:
  birs_freesymbs bs sbs =
      ((BIGUNION (IMAGE birs_symb_symbols sbs)) DIFF (birs_symb_symbols bs))
Proof
  fs [birs_freesymbs_def, birs_symb_symbols_set_def]
QED

Theorem birs_freesymbs_EQ_thm:
  !prog L bs sbs.
  birs_freesymbs bs sbs = symb_freesymbs (bir_symb_rec_sbir prog) (birs_symb_to_symbst bs, L, IMAGE birs_symb_to_symbst sbs)
Proof
  REWRITE_TAC [birs_freesymbs_thm, symb_freesymbs_def] >>
  REWRITE_TAC [birs_auxTheory.symb_symbols_set_ALT_thm] >>
  REWRITE_TAC [pred_setTheory.IMAGE_IMAGE, combinTheory.o_DEF, birs_symb_symbols_EQ_thm] >>
  METIS_TAC []
QED



(* ******************************************************* *)
(*      ASSERT statement justification                     *)
(* ******************************************************* *)
(* this is an adjusted copy of "bir_disj1_false" from "bir_exp_equivTheory" *)
local
  open bir_bool_expTheory
in
Theorem bir_conj_true:
  !A B.
      (bir_eval_bin_exp BIExp_And (A) (B) = SOME bir_val_true) ==>
      (A = SOME bir_val_true /\
       B = SOME bir_val_true)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def,
                                      bir_val_false_def] >> (
  Cases_on `A` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `B` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `b` >> Cases_on `b'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_exp_def]
  ) >>
  blastLib.FULL_BBLAST_TAC
)
QED
end;

Theorem birs_pcondwiden_AND_thm:
  !pre cond.
  birs_pcondwiden (BExp_BinExp BIExp_And pre cond) pre
Proof
REWRITE_TAC [birs_pcondwiden_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  METIS_TAC [bir_conj_true]
QED


Theorem assert_spec_thm:
  !bprog bs L lbl1 env1 status pre cond lbl2 env2.
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>;
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := BST_AssertionViolated;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>})) ==>
  (lbl1 <> lbl2 \/
   status <> BST_AssertionViolated) ==>
  (birs_pcondinf (BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond))) ==>
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status;
        bsst_pcond := pre|>}))
Proof
    REWRITE_TAC [birs_symb_exec_def] >>
    REPEAT STRIP_TAC >> (
    IMP_RES_TAC symb_rulesTheory.symb_rule_INF_thm >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ``birs_symb_to_symbst <|bsst_pc := lbl2; bsst_environ := env2;
                  bsst_status := BST_AssertionViolated;
                  bsst_pcond :=
                    BExp_BinExp BIExp_And pre (BExp_UnaryExp BIExp_Not cond)|>``) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [IMAGE_INSERT, IMAGE_EMPTY, birs_symb_to_symbst_def] >>

    `symb_pcondinf (bir_symb_rec_sbir bprog)
          (BExp_BinExp BIExp_And pre (BExp_UnaryExp BIExp_Not cond))` by (
      METIS_TAC [birs_pcondinf_thm, symb_symbst_pcond_def]
    ) >>

    FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [symb_symbst_pcond_def, DIFF_INSERT, DIFF_EMPTY, DELETE_INSERT, EMPTY_DELETE] >>
    REV_FULL_SIMP_TAC (std_ss) [] >>

    Q.ABBREV_TAC `sys = SymbSymbSt bs.bsst_pc bs.bsst_environ bs.bsst_pcond bs.bsst_status` >>
    Q.ABBREV_TAC `sys2 = SymbSymbSt lbl1 env1 (BExp_BinExp BIExp_And pre cond) status` >>
    Q.ABBREV_TAC `sys2' = SymbSymbSt lbl1 env1 pre status` >>

    ASSUME_TAC (
      (Q.SPECL [`sys`, `L`, `{sys2}`, `sys2`, `sys2'`] o
       SIMP_RULE std_ss [bir_symb_soundTheory.birs_symb_ARB_val_sound_thm] o
       MATCH_MP symb_rulesTheory.symb_rule_CONS_E_thm o
       Q.SPEC `bprog`)
         bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>

    `symb_pcondwiden_sys (bir_symb_rec_sbir bprog) sys2 sys2'` by (
      Q.UNABBREV_TAC `sys2` >>
      Q.UNABBREV_TAC `sys2'` >>

      SIMP_TAC (std_ss++symb_TYPES_ss) [symb_rulesTheory.symb_pcondwiden_sys_def, symb_symbst_extra_def, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_pcond_def] >>
      REWRITE_TAC [birs_pcondwiden_thm, birs_pcondwiden_AND_thm]
    ) >>

    FULL_SIMP_TAC (std_ss) [] >>
    REV_FULL_SIMP_TAC (std_ss) [DIFF_INSERT, SING_DELETE, DIFF_EMPTY, UNION_EMPTY]
  )
QED


Theorem branch_prune1_spec_thm:
  !bprog bs L lbl1 env1 status1 pre cond lbl2 env2 status2.
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status1;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>;
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := status2;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>})) ==>
  (lbl1 <> lbl2 \/
   status1 <> status2) ==>
  (birs_pcondinf (BExp_BinExp BIExp_And pre cond)) ==>
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := status2;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>}))
Proof
  REWRITE_TAC [birs_symb_exec_def] >>
  REPEAT STRIP_TAC >> (
    IMP_RES_TAC symb_rulesTheory.symb_rule_INF_thm >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ``birs_symb_to_symbst <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status1;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>``) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [IMAGE_INSERT, IMAGE_EMPTY, birs_symb_to_symbst_def] >>

    `symb_pcondinf (bir_symb_rec_sbir bprog)
          (BExp_BinExp BIExp_And pre cond)` by (
      METIS_TAC [birs_pcondinf_thm, symb_symbst_pcond_def]
    ) >>

    FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [symb_symbst_pcond_def, DIFF_INSERT, DIFF_EMPTY, DELETE_INSERT, EMPTY_DELETE] >>
    REV_FULL_SIMP_TAC (std_ss) []
  )
QED


Theorem branch_prune2_spec_thm:
  !bprog bs L lbl1 env1 status1 pre cond lbl2 env2 status2.
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status1;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>;
      <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := status2;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>})) ==>
  (lbl1 <> lbl2 \/
   status1 <> status2) ==>
  (birs_pcondinf (BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond))) ==>
  (birs_symb_exec bprog
    (bs, L, {
      <|bsst_pc := lbl1;
        bsst_environ := env1;
        bsst_status := status1;
        bsst_pcond := BExp_BinExp BIExp_And pre cond|>}))
Proof
    REWRITE_TAC [birs_symb_exec_def] >>
    REPEAT STRIP_TAC >> (
    IMP_RES_TAC symb_rulesTheory.symb_rule_INF_thm >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ``birs_symb_to_symbst <|bsst_pc := lbl2;
        bsst_environ := env2;
        bsst_status := status2;
        bsst_pcond := BExp_BinExp BIExp_And pre
                 (BExp_UnaryExp BIExp_Not cond)|>``) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [IMAGE_INSERT, IMAGE_EMPTY, birs_symb_to_symbst_def] >>

    `symb_pcondinf (bir_symb_rec_sbir bprog)
          (BExp_BinExp BIExp_And pre (BExp_UnaryExp BIExp_Not cond))` by (
      METIS_TAC [birs_pcondinf_thm, symb_symbst_pcond_def]
    ) >>

    FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [symb_symbst_pcond_def, DIFF_INSERT, DIFF_EMPTY, DELETE_INSERT, EMPTY_DELETE] >>
    REV_FULL_SIMP_TAC (std_ss) []
  )
QED


(* ******************************************************* *)
(*      CONSEQUENCE rule                                   *)
(* ******************************************************* *)
Definition birs_symb_pcondwiden_sys_def:
  birs_symb_pcondwiden_sys bs bs' =
    (
      bs.bsst_status = bs'.bsst_status /\
      bs.bsst_pc = bs'.bsst_pc /\
      bs.bsst_environ = bs'.bsst_environ /\
      birs_exp_imp bs.bsst_pcond bs'.bsst_pcond
    )
End

Theorem birs_symb_pcondwiden_sys_thm:
  !prog bs bs'.
    symb_pcondwiden_sys (bir_symb_rec_sbir prog) (birs_symb_to_symbst bs) (birs_symb_to_symbst bs') =
    birs_symb_pcondwiden_sys bs bs'
Proof
  Cases_on `bs` >> Cases_on `bs'` >>
  fs [birs_symb_pcondwiden_sys_def,
      symb_rulesTheory.symb_pcondwiden_sys_def,
      GSYM symb_exp_imp_EQ_pcondwiden_thm,
      birs_exp_imp_thm, birs_symb_to_symbst_def,
      symb_symbst_pc_def, symb_symbst_store_def,
      symb_symbst_pcond_def, symb_symbst_extra_def]
QED

Theorem birs_rule_WIDEN_thm:
  !prog L bs bs2 bs2' Pi.
    birs_symb_pcondwiden_sys bs2 bs2' ==>
    birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
    birs_symb_exec prog (bs, L, bs2' INSERT Pi)
Proof
  rpt strip_tac >>
  assume_tac (
    (SIMP_RULE std_ss [
      GSYM birs_symb_exec_def,
      GSYM birs_freesymbs_EQ_thm,
      bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm,
      birs_symb_pcondwiden_sys_thm,
      SIMP_RULE std_ss [pred_setTheory.IMAGE_SING] (Q.SPECL [`Pi`, `bs2`, `{bs2'}`] bestTheorem)
    ] o
    Q.SPECL [`birs_symb_to_symbst bs`, `L`, `IMAGE birs_symb_to_symbst (bs2 INSERT Pi)`, `birs_symb_to_symbst bs2`, `birs_symb_to_symbst bs2'`] o
     SIMP_RULE std_ss [
          bir_symb_soundTheory.birs_symb_ARB_val_sound_thm
          ] o
       MATCH_MP symb_rulesTheory.symb_rule_CONS_E_thm o Q.SPEC `prog` (* symb_rulesTheory.symb_rule_CONS_thm *)
    ) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  ‘birs_symb_exec prog (bs, L, bs2' INSERT (Pi DELETE bs2))’ by (
    gvs [INSERT_SING_DIFF_ALT_thm]
  ) >>
  metis_tac [birs_symb_exec_INSERT_DELETE_thm]
QED

Theorem birs_rule_WIDEN_spec_thm:
  !prog bs L bs2 Pi pcond' bs2'.
   (bs2' =
     <|bsst_pc := bs2.bsst_pc;
       bsst_environ := bs2.bsst_environ;
       bsst_status := bs2.bsst_status;
       bsst_pcond := pcond'|>) ==>
    birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
    birs_exp_imp bs2.bsst_pcond pcond' ==>
    birs_symb_exec prog (bs, L, bs2' INSERT Pi)
Proof
  rpt strip_tac >>
  `birs_symb_pcondwiden_sys bs2 bs2'` by (
    fs [birs_symb_pcondwiden_sys_def]
  ) >>
  METIS_TAC [birs_rule_WIDEN_thm]
QED

Theorem birs_rule_WIDEN_spec_thm2 =
  SIMP_RULE std_ss [] birs_rule_WIDEN_spec_thm;

Theorem birs_rule_NARROW_thm:
  !prog L bs1 bs1' Pi.
    birs_symb_pcondwiden_sys bs1 bs1' ==>
    birs_symb_symbols bs1 INTER birs_freesymbs bs1' Pi = EMPTY ==>
    birs_symb_exec prog (bs1', L, Pi) ==>
    birs_symb_exec prog (bs1, L, Pi)
Proof
  rpt strip_tac >>
  assume_tac (
    (SIMP_RULE std_ss [
      GSYM birs_symb_exec_def,
      GSYM symb_recordTheory.symb_freesymbs_def,
      GSYM birs_freesymbs_EQ_thm,
      bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm,
      birs_symb_pcondwiden_sys_thm
      ] o
     REWRITE_RULE [(GSYM o Q.ISPEC `IMAGE birs_symb_to_symbst Pi` o ISPEC ``L:bir_programcounter_t->bool`` o Q.ISPECL [`bir_symb_rec_sbir prog`, `birs_symb_to_symbst bs1'`]) symb_freesymbs_def]       o
    Q.SPECL [`birs_symb_to_symbst bs1'`, `birs_symb_to_symbst bs1`, `L`, `IMAGE birs_symb_to_symbst Pi`] o
     SIMP_RULE std_ss [
          bir_symb_soundTheory.birs_symb_ARB_val_sound_thm
          ] o
       MATCH_MP symb_rulesTheory.symb_rule_CONS_S_thm o Q.SPEC `prog` (* symb_rulesTheory.symb_rule_CONS_thm *)
    ) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  gvs []
QED

Theorem birs_rule_NARROW_spec_thm:
  !prog L bs1' Pi pcond' bs1.
   (bs1 =
     <|bsst_pc := bs1'.bsst_pc;
       bsst_environ := bs1'.bsst_environ;
       bsst_status := bs1'.bsst_status;
       bsst_pcond := pcond'|>) ==>
    birs_symb_exec prog (bs1', L, Pi) ==>
    birs_exp_imp pcond' bs1'.bsst_pcond ==>
    birs_symb_symbols bs1 INTER birs_freesymbs bs1' Pi = EMPTY ==>
    birs_symb_exec prog (bs1, L, Pi)
Proof
  rpt strip_tac >>
  `birs_symb_pcondwiden_sys bs1 bs1'` by (
    fs [birs_symb_pcondwiden_sys_def]
  ) >>
  METIS_TAC [birs_rule_NARROW_thm]
QED

Theorem birs_rule_NARROW_spec_thm2 =
  SIMP_RULE std_ss [] birs_rule_NARROW_spec_thm;


(* ******************************************************* *)
(*      SRENAME and INST rule                              *)
(* ******************************************************* *)
(*
Theorem birs_rule_RENAME_MANY_thm:
  !prog L bs Pi rens.
    FUPDATE_LIST FEMPTY (MAP (\(x,y). (x, BExp_Den y)) rens) = s ==>
    set (MAP SND rens) INTER (birs_symb_symbols bs UNION birs_symb_symbols_set Pi) = EMPTY ==>
    birs_symb_exec prog (bs, L, Pi) ==>
    birs_symb_exec prog (birs_symb_subst s bs, L, IMAGE (birs_symb_subst s) Pi)
Proof
  (* TODO: problem with proof when multiple operations all at once, would need to argue with arbitrary choice of symbols that are not present in the states, and that there is always such a choice *)
  (* symb_rulesTheory.symb_rule_SRENAME_thm *)
  cheat
QED
*)

Theorem birs_rule_RENAME1_thm[local]:
  !prog L bs Pi alpha alpha'.
    bir_var_type alpha = bir_var_type alpha' ==>
    alpha' NOTIN (birs_symb_symbols bs UNION birs_symb_symbols_set Pi) ==>
    birs_symb_exec prog (bs, L, Pi) ==>
    birs_symb_exec prog (birs_symb_subst1 (alpha, BExp_Den alpha') bs, L, IMAGE (birs_symb_subst1 (alpha, BExp_Den alpha')) Pi)
Proof
  rpt strip_tac >>
  assume_tac (
    (CONV_RULE (LAND_CONV (SIMP_CONV (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def])) o
    SIMP_RULE std_ss [
      GSYM birs_symb_exec_def,
      birs_symb_symbols_set_EQ_thm2,
      bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm
    ] o
    Q.SPECL [`birs_symb_to_symbst bs`, `L`, `IMAGE birs_symb_to_symbst Pi`, `alpha`, `alpha'`] o
     SIMP_RULE std_ss [
          bir_symb_soundTheory.birs_symb_symbols_f_sound_thm,
          bir_symb_soundTheory.birs_symb_subst_f_sound_thm,
          bir_symb_soundTheory.birs_symb_subst_f_sound_NOTIN_thm,
          bir_symb_soundTheory.birs_symb_mk_exp_symb_f_sound_thm,
          bir_symb_soundTheory.birs_symb_mk_exp_symb_f_sound_typeof_thm
          ] o
       MATCH_MP symb_rulesTheory.symb_rule_SRENAME_thm o Q.SPEC `prog`
      ) bir_symb_soundTheory.birs_symb_typeof_exp_sound_thm) >>
  gvs [] >>

  fs [symb_recordTheory.symb_subst_set_def, bir_symb_soundTheory.birs_symb_subst1_EQ_thm,
      bir_symb_soundTheory.birs_symb_subst1_set_EQ_thm, GSYM birs_symb_exec_def] >>

  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def]
QED

Theorem birs_rule_RENAME1_spec_thm:
  !prog L bs Pi alpha alpha'.
    birs_symb_exec prog (bs, L, Pi) ==>
    bir_var_type alpha = bir_var_type alpha' ==>
    alpha' NOTIN birs_symb_symbols bs ==>
    alpha' NOTIN birs_symb_symbols_set Pi ==>
    birs_symb_exec prog (birs_symb_subst1 (alpha, BExp_Den alpha') bs, L, IMAGE (birs_symb_subst1 (alpha, BExp_Den alpha')) Pi)
Proof
  fs [birs_rule_RENAME1_thm]
QED

Theorem birs_rule_INST1_thm:
  !prog L bs Pi alpha bexp.
    birs_symb_exec prog (bs, L, Pi) ==>
    type_of_bir_exp bexp = SOME (bir_var_type alpha) ==>
    alpha IN birs_symb_symbols bs ==>
    bir_vars_of_exp bexp INTER birs_freesymbs bs Pi = EMPTY ==>
    birs_symb_exec prog (birs_symb_subst1 (alpha, bexp) bs, L, IMAGE (birs_symb_subst1 (alpha, bexp)) Pi)
Proof
  rpt strip_tac >>
  assume_tac (
    (SIMP_RULE std_ss [
      GSYM birs_symb_exec_def,
      GSYM birs_freesymbs_EQ_thm,
      bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm
    ] o
    Q.SPECL [`birs_symb_to_symbst bs`, `L`, `IMAGE birs_symb_to_symbst Pi`, `alpha`, `bexp`] o
     SIMP_RULE std_ss [
          bir_symb_soundTheory.birs_symb_subst_f_sound_thm,
          bir_symb_soundTheory.birs_symb_symbols_f_sound_thm
          ] o
       MATCH_MP symb_rulesTheory.symb_rule_INST_thm o Q.SPEC `prog`
      ) bir_symb_soundTheory.birs_symb_typeof_exp_sound_thm) >>

  fs [symb_recordTheory.symb_subst_set_def, bir_symb_soundTheory.birs_symb_subst1_EQ_thm,
      bir_symb_soundTheory.birs_symb_subst1_set_EQ_thm, GSYM birs_symb_exec_def] >>

  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def]
QED


(* ******************************************************* *)
(*      FREESYMB rule                                      *)
(* ******************************************************* *)
Theorem birs_rule_FREESYMB_INTRO_thm:
  !prog L bs bs2 bs2' Pi alpha bexp vn symbexp symbexp' pcond'.
    bir_type_is_Imm (bir_var_type alpha) ==>
    bs2.bsst_environ vn = SOME symbexp ==>
    (BExp_BinExp BIExp_And (BExp_BinPred BIExp_Equal (BExp_Den alpha) bexp)) bs2.bsst_pcond = pcond' ==>
    alpha NOTIN birs_symb_symbols bs ==>
    alpha NOTIN birs_symb_symbols bs2 ==>
    bir_vars_of_exp bexp SUBSET birs_symb_symbols bs2 ==>
    type_of_bir_exp bexp = SOME (bir_var_type alpha) ==>
    birs_simplification pcond' symbexp symbexp' ==>
    ((bs2 with bsst_pcond := pcond') with bsst_environ := birs_update_env (vn,symbexp') bs2.bsst_environ) = bs2' ==>
    birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
    birs_symb_exec prog (bs, L, bs2' INSERT Pi)
Proof
  rpt strip_tac >>

  `symb_symbst_store (birs_symb_to_symbst bs2) vn = bs2.bsst_environ vn` by (
    Cases_on `bs2` >>
    fs [birs_symb_to_symbst_def, symb_symbst_pc_def, symb_symbst_store_def, symb_symbst_pcond_def, symb_symbst_extra_def]    
  ) >>

  `symb_symbst_pcond_update
                (symb_expr_conj_eq (bir_symb_rec_sbir prog)
                   ((bir_symb_rec_sbir prog).sr_mk_exp_symb_f alpha) bexp)
                (symb_symbst_store_update vn symbexp'
                   (birs_symb_to_symbst bs2)) = birs_symb_to_symbst bs2' /\
   symb_symbst_pcond (birs_symb_to_symbst bs2') = pcond'` by (
    Cases_on `bs2` >> Cases_on `bs2'` >>

(*
dest_comb “birs_state_t b f b0 b1 with
        <|bsst_environ :=
            birs_update_env (vn,symbexp')
              (birs_state_t b f b0 b1).bsst_environ; bsst_pcond := pcond'|>”

bir_symbTheory.birs_state_t_fupdcanon
bir_symbTheory.birs_state_t_fupdfupds
bir_symbTheory.recordtype_birs_state_t_seldef_bsst_environ_fupd_def
bir_symbTheory.birs_state_t_literal_11
*)
    FULL_SIMP_TAC (std_ss++birs_state_ss) [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM, bir_symbTheory.birs_state_t_fn_updates] >>

    fs [birs_symb_to_symbst_def, symb_symbst_pcond_def, symb_symbst_pcond_update_def, symb_symbst_store_update_def, bir_symb_soundTheory.birs_symb_expr_conj_eq_thm] >>
    SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def] >>

    fs [birs_update_env_def] >>

    `?bt. type_of_bir_exp (BExp_Den alpha) = SOME (BType_Imm bt)` by (
      fs [bir_valuesTheory.bir_type_is_Imm_def, bir_typing_expTheory.type_of_bir_exp_def]
    ) >>
    fs [bir_symb_soundTheory.birs_symb_expr_conj_eq_thm2]
  ) >>

  assume_tac (
    (SIMP_RULE std_ss [
      GSYM birs_symb_exec_def,
      birs_simplification_thm,
      birs_symb_symbols_set_EQ_thm2,
      bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm
    ] o
    Q.SPECL [`birs_symb_to_symbst bs`, `L`, `IMAGE birs_symb_to_symbst (bs2 INSERT Pi)`, `birs_symb_to_symbst bs2`, `vn`, `bexp`, `alpha`, `symbexp`, `symbexp'`] o
    SIMP_RULE std_ss [
          bir_symb_soundTheory.birs_symb_typeof_exp_sound_thm,
          bir_symb_soundTheory.birs_symb_val_eq_sound_thm,
          bir_symb_soundTheory.birs_symb_mk_exp_eq_f_sound_thm,
          bir_symb_soundTheory.birs_symb_mk_exp_conj_f_sound_thm,
          bir_symb_soundTheory.birs_symb_mk_exp_symb_f_sound_thm,
          bir_symb_soundTheory.birs_symb_ARB_val_sound_thm
          ] o
       MATCH_MP symb_rulesTheory.symb_rule_FRESH_thm o Q.SPEC `prog`
    ) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  rev_full_simp_tac std_ss [] >>

  pop_assum (assume_tac o CONV_RULE (LAND_CONV (SIMP_CONV (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def]))) >>
  rev_full_simp_tac std_ss [] >>
  pop_assum (assume_tac o CONV_RULE (LAND_CONV (SIMP_CONV (std_ss++symb_typesLib.symb_TYPES_ss) [bir_symbTheory.bir_symb_rec_sbir_def]))) >>
  rev_full_simp_tac std_ss [] >>

  rev_full_simp_tac std_ss [GSYM birs_symb_exec_def,SIMP_RULE std_ss [pred_setTheory.IMAGE_SING] (Q.SPECL [`bs2 INSERT Pi`, `bs2`, `{bs2'}`] bestTheorem)] >>

  ‘birs_symb_exec prog (bs, L, bs2' INSERT (Pi DELETE bs2))’ by (
    gvs [INSERT_SING_DIFF_ALT_thm]
  ) >>
  metis_tac [birs_symb_exec_INSERT_DELETE_thm]
QED

Theorem birs_rule_FREESYMB_INTRO_thm2:
  !prog bs L bs2 Pi bs2' alpha bexp vn symbexp symbexp' pcond'.
    pcond' = (BExp_BinExp BIExp_And (BExp_BinPred BIExp_Equal (BExp_Den alpha) bexp)) bs2.bsst_pcond ==>
    (bs2' =
     <|bsst_pc := bs2.bsst_pc;
       bsst_environ := birs_update_env (vn,symbexp') bs2.bsst_environ;
       bsst_status := bs2.bsst_status;
       bsst_pcond := pcond'|>) ==>
    birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
    type_of_bir_exp bexp = SOME (bir_var_type alpha) ==>
    bir_type_is_Imm (bir_var_type alpha) ==>
    bs2.bsst_environ vn = SOME symbexp ==>
    alpha NOTIN birs_symb_symbols bs ==>
    alpha NOTIN birs_symb_symbols bs2 ==>
    bir_vars_of_exp bexp SUBSET birs_symb_symbols bs2 ==>
    birs_simplification pcond' symbexp symbexp' ==>
    birs_symb_exec prog (bs, L, bs2' INSERT Pi)
Proof
  rpt strip_tac >>
  `bs2' = bs2 with
       <|bsst_environ := birs_update_env (vn,symbexp') bs2.bsst_environ;
         bsst_pcond := pcond'|>` by (
    Q.PAT_ASSUM ‘A = bsst_pc_fupd B C’ (fn thm => rpt (pop_assum (K ALL_TAC)) >> assume_tac (thm)) >>
    fs [] >> pop_assum (K ALL_TAC) >>
    Cases_on ‘bs2’ >> Cases_on ‘ARB:birs_state_t’ >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [bir_symbTheory.birs_state_t_fn_updates]
  ) >>
  metis_tac [birs_rule_FREESYMB_INTRO_thm]
QED

Theorem birs_rule_FREESYMB_INTRO_spec_thm =
  SIMP_RULE std_ss [] birs_rule_FREESYMB_INTRO_thm2;


(* ******************************************************* *)
(*      SUBST rule                                         *)
(* ******************************************************* *)
Theorem symb_rule_SUBST_thm[local]:
  !sr.
!sys L sys2 var symbexp symbexp' Pi.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, sys2 INSERT Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>

  (symb_simplification sr (symb_symbst_pcond sys2) symbexp symbexp') ==>

  (symb_hl_step_in_L_sound sr (sys, L, (symb_symbst_store_update var symbexp' sys2) INSERT (Pi DELETE sys2)))
Proof
  REPEAT STRIP_TAC >>
  METIS_TAC [INSERT_SING_DIFF_ALT_thm, symb_rulesTheory.symb_rule_SUBST_thm]
QED

Theorem symb_rule_SUBST_SING_thm[local]:
  !sr.
!sys L sys2 var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>
  (symb_ARB_val_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, {sys2})) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>

  (symb_simplification sr (symb_symbst_pcond sys2) symbexp symbexp') ==>

  (symb_hl_step_in_L_sound sr (sys, L, {symb_symbst_store_update var symbexp' sys2}))
Proof
  REPEAT STRIP_TAC >>

  METIS_TAC [symb_rule_SUBST_thm, EMPTY_DELETE]
QED

(* TODO: move to bir_symbScript.sml *)
Theorem birs_symb_to_symbst_IMAGE_DELETE_thm:
!x s.
  IMAGE birs_symb_to_symbst s DELETE birs_symb_to_symbst x =
  IMAGE birs_symb_to_symbst (s DELETE x)
Proof
  simp_tac std_ss [EXTENSION, IN_DELETE, IN_IMAGE] >>
  metis_tac [birs_symb_to_symbst_EXISTS_thm, birs_symb_from_symbst_EXISTS_thm, birs_symb_to_from_symbst_thm]
QED

Theorem birs_rule_SUBST_thm1:
  !prog bs2 bs2' bs L lbl status pcond envl vn symbexp Pi symbexp'.
           (bs2 =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           (bs2' =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
           birs_simplification pcond symbexp symbexp' ==>
           birs_symb_exec prog (bs, L, bs2' INSERT (Pi DELETE bs2))
Proof
  REWRITE_TAC [birs_symb_exec_def, IMAGE_INSERT] >>
  REPEAT STRIP_TAC >>
  ASSUME_TAC (
    (Q.SPECL [`birs_symb_to_symbst bs`, `L`, `birs_symb_to_symbst bs2`, `vn`, `symbexp`, `symbexp'`, `IMAGE birs_symb_to_symbst Pi`] o
     SIMP_RULE std_ss [bir_symb_soundTheory.birs_symb_ARB_val_sound_thm] o
     MATCH_MP symb_rule_SUBST_thm o
     Q.SPEC `prog`)
       bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>

  FULL_SIMP_TAC std_ss [birs_symb_to_symbst_IMAGE_DELETE_thm] >>

  REV_FULL_SIMP_TAC (std_ss++birs_state_ss)
    [IMAGE_SING, birs_symb_to_symbst_def, symb_symbst_store_def, symb_symbst_pcond_def,
     birs_simplification_thm,
     symb_symbst_store_update_def, birs_auxTheory.birs_gen_env_thm,
     combinTheory.UPDATE_APPLY]
QED

Theorem birs_rule_SUBST_thm:
  !prog bs2 bs2' bs L lbl status pcond envl vn symbexp Pi symbexp'.
           (bs2 =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           (bs2' =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           birs_symb_exec prog (bs, L, bs2 INSERT Pi) ==>
           birs_simplification pcond symbexp symbexp' ==>
           birs_symb_exec prog (bs, L, bs2' INSERT Pi)
Proof
  metis_tac [birs_rule_SUBST_thm1, birs_symb_exec_INSERT_DELETE_thm]
QED

Theorem birs_rule_SUBST_spec_thm:
  !prog bs2 bs2' bs L lbl status pcond envl vn symbexp symbexp'.
           (bs2 =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           (bs2' =
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>) ==>
           birs_symb_exec prog (bs, L, {bs2}) ==>
           birs_simplification pcond symbexp symbexp' ==>
           birs_symb_exec prog (bs, L, {bs2'})
Proof
  metis_tac [birs_rule_SUBST_thm]
QED




(* ******************************************************* *)
(*      STEP rule                                          *)
(* ******************************************************* *)
Theorem birs_rule_STEP_gen1_thm:
  !prog sys.
  (bir_prog_has_no_halt prog) ==>

  (symb_hl_step_in_L_sound (bir_symb_rec_sbir prog)
    (sys,
     {symb_symbst_pc sys},
     IMAGE birs_symb_to_symbst
       (birs_exec_step prog (birs_symb_from_symbst sys))))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_symb_soundTheory.birs_symb_step_sound_thm >>

  IMP_RES_TAC symb_rulesTheory.symb_rule_STEP_thm >>
  POP_ASSUM (ASSUME_TAC o SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss) [] o REWRITE_RULE [Once bir_symbTheory.bir_symb_rec_sbir_def]) >>

  METIS_TAC [IN_SING]
QED

Theorem birs_rule_STEP_gen2_thm:
  !prog bsys.
  (bir_prog_has_no_halt prog) ==>

  (birs_symb_exec prog
    (bsys,
     {bsys.bsst_pc},
     (birs_exec_step prog bsys)))
Proof
  REWRITE_TAC [birs_symb_exec_def] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_rule_STEP_gen1_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `birs_symb_to_symbst bsys`) >>

  FULL_SIMP_TAC std_ss [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_auxTheory.birs_symb_symbst_pc_thm]
QED


(* ******************************************************* *)
(*      SEQ rule                                           *)
(* ******************************************************* *)
val betterTheorem = prove(``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (symb_hl_step_in_L_sound sr (sys_B, L_B, Pi_B)) ==>

  (* can't reintroduce symbols in fragment B that have been lost in A *)
  ((symb_symbols sr sys_A) INTER (symb_freesymbs sr (sys_B, L_B, Pi_B)) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, (Pi_A DIFF {sys_B}) UNION Pi_B))
``,
  METIS_TAC[symb_rulesTheory.symb_rule_SEQ_thm]
);

Theorem birs_rule_SEQ_gen_thm:
  !prog bsys_A L_A bPi_A bsys_B L_B bPi_B.
  (birs_symb_exec prog (bsys_A, L_A, bPi_A)) ==>
  (birs_symb_exec prog (bsys_B, L_B, bPi_B)) ==>

  ((birs_symb_symbols bsys_A) INTER (birs_freesymbs bsys_B bPi_B) = EMPTY) ==>

  (birs_symb_exec prog (bsys_A, L_A UNION L_B, (bPi_A DIFF {bsys_B}) UNION bPi_B))
Proof
  REWRITE_TAC [birs_symb_exec_def] >>
  REPEAT GEN_TAC >>
  REWRITE_TAC [ISPECL [``prog: 'a bir_program_t``, ``L_B:bir_programcounter_t -> bool``, ``bsys_B:birs_state_t``, ``bPi_B:birs_state_t -> bool``] birs_freesymbs_EQ_thm] >>
  REWRITE_TAC [GSYM birs_symb_symbols_EQ_thm] >>
  REPEAT STRIP_TAC >>
  ASSUME_TAC (ISPEC ``prog: 'a bir_program_t`` bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  METIS_TAC [betterTheorem, bestTheorem]
QED


(* ******************************************************* *)
(*      NO FREE SYMBS                                      *)
(* ******************************************************* *)
Definition birs_freesymbs_SING_def:
  birs_freesymbs_SING bs1 bs2 =
      ((birs_symb_symbols bs2) DIFF (birs_symb_symbols bs1))
End

Definition birs_freesymbs_EMPTY_def:
  birs_freesymbs_EMPTY bs sbs =
      (birs_freesymbs bs sbs = EMPTY)
End

Definition birs_freesymbs_SING_EMPTY_def:
  birs_freesymbs_SING_EMPTY bs1 bs2 =
      (birs_freesymbs_SING bs1 bs2 = EMPTY)
End

Theorem birs_freesymbs_SING_EMPTY_SUFFICIENT_thm:
  !bs1 bs2.
  (bs1.bsst_environ = bs2.bsst_environ /\
   bs1.bsst_pcond   = bs2.bsst_pcond) ==>
  (birs_freesymbs_SING_EMPTY bs1 bs2)
Proof
SIMP_TAC std_ss [birs_freesymbs_SING_EMPTY_def, birs_freesymbs_SING_def, birs_symb_symbols_def, DIFF_EQ_EMPTY]
QED

Theorem birs_freesymbs_SING_EMPTY_SUFFICIENT2_thm:
  !bs1 bs2 bs2'.
  (birs_freesymbs_SING_EMPTY bs1 bs2 /\
   bs2.bsst_environ = bs2'.bsst_environ /\
   bs2.bsst_pcond   = bs2'.bsst_pcond) ==>
  (birs_freesymbs_SING_EMPTY bs1 bs2')
Proof
SIMP_TAC std_ss [birs_freesymbs_SING_EMPTY_def, birs_freesymbs_SING_def, birs_symb_symbols_def, DIFF_EQ_EMPTY] >>
  REPEAT STRIP_TAC >>
  METIS_TAC []
QED

(* TODO: this should go to auxTheory *)
Theorem SUBSET_of_DIFF_2_thm:
  !s t v.
    s SUBSET t ==>
    ((v DIFF t) SUBSET (v DIFF s))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF] >>
  METIS_TAC []
QED

Theorem birs_freesymbs_SING_EMPTY_SUFFICIENT3_thm:
  !bs1 bs1' bs2.
  (birs_freesymbs_SING_EMPTY bs1 bs2 /\
   (birs_symb_symbols bs1) SUBSET (birs_symb_symbols bs1')) ==>
  (birs_freesymbs_SING_EMPTY bs1' bs2)
Proof
SIMP_TAC std_ss [birs_freesymbs_SING_EMPTY_def, birs_freesymbs_SING_def, DIFF_EQ_EMPTY] >>
  REPEAT STRIP_TAC >>

  METIS_TAC [SUBSET_of_DIFF_2_thm, SUBSET_EMPTY]
QED

Theorem BIGUNION_IMAGE_DIFF_EQ_thm:
  !f s1 s2s.
  ((BIGUNION (IMAGE f s2s)) DIFF s1 = BIGUNION (IMAGE (\s2. (f s2) DIFF s1) s2s))
Proof
SIMP_TAC (std_ss) [EXTENSION, IN_BIGUNION_IMAGE, IN_DIFF] >>
  METIS_TAC []
QED

Theorem birs_freesymbs_thm2:
  !bs sbs.
  (birs_freesymbs bs sbs = BIGUNION (IMAGE (\bs2. birs_freesymbs_SING bs bs2) sbs))
Proof
SIMP_TAC std_ss [birs_freesymbs_thm, birs_freesymbs_SING_def, BIGUNION_IMAGE_DIFF_EQ_thm]
QED

Theorem birs_freesymbs_EMPTY_thm:
  !bs sbs.
  (birs_freesymbs_EMPTY bs sbs =
   !bs2. bs2 IN sbs ==> (birs_freesymbs_SING_EMPTY bs bs2))
Proof
SIMP_TAC std_ss [birs_freesymbs_EMPTY_def, birs_freesymbs_thm2, birs_freesymbs_SING_EMPTY_def] >>
  SIMP_TAC (std_ss) [EXTENSION, IN_BIGUNION_IMAGE, NOT_IN_EMPTY] >>
  METIS_TAC []
QED

Theorem birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm:
  !bsys be sv ty pcond'.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty) /\
   bir_vars_of_exp pcond' = bir_vars_of_exp bsys.bsst_pcond UNION bir_vars_of_exp sv) ==>
  (birs_symb_symbols bsys =
   birs_symb_symbols (bsys with bsst_pcond := pcond'))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm >>

  ASM_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def] >>
  IMP_RES_TAC SUBSET_UNION_ABSORPTION >>

  METIS_TAC [UNION_COMM, UNION_ASSOC]
QED

Theorem birs_eval_exp_IMP_symb_symbols_EQ_pcond_status_thm:
  !bsys be sv ty pcond' status'.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty) /\
   bir_vars_of_exp pcond' = bir_vars_of_exp bsys.bsst_pcond UNION bir_vars_of_exp sv) ==>
  (birs_symb_symbols bsys =
   birs_symb_symbols (bsys with <|bsst_status := status'; bsst_pcond := pcond'|>))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>

  ASM_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def]
QED

(* TODO: this definition needs to go somewhere else and must be integrated with the other places where it belongs (into previous definitions and proofs) *)
Definition birs_vars_of_env_def:
  birs_vars_of_env senv =
      BIGUNION {bir_vars_of_exp e | (?vn. senv vn = SOME e)}
End

(*
TODO: these two theorems are the same, did I prove them twice? (bir_symbTheory should be "before")
bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm
bir_symb_soundTheory.birs_eval_exp_IMP_varset_thm
*)
Theorem birs_eval_exp_IMP_symbs_SUBSET_senv_thm:
  !e senv sv ty.
       birs_eval_exp e senv = SOME (sv,ty) ==>
       bir_vars_of_exp sv SUBSET birs_vars_of_env senv
Proof
METIS_TAC [bir_symbTheory.bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm, birs_vars_of_env_def]
QED

Theorem birs_eval_exp_IMP_vars_of_env_SUBSET_thm:
  !env be sv ty vn.
  (birs_eval_exp be env = SOME (sv,ty)) ==>
  (birs_vars_of_env (birs_update_env (vn,sv) env) SUBSET (birs_vars_of_env env))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_symbs_SUBSET_senv_thm >>

  FULL_SIMP_TAC (std_ss) [SUBSET_DEF] >>

  FULL_SIMP_TAC (std_ss) [birs_vars_of_env_def] >>
  FULL_SIMP_TAC (std_ss) [FORALL_IN_BIGUNION] >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Cases_on `vn = vn'` >> (
    FULL_SIMP_TAC (std_ss) [birs_update_env_def, combinTheory.UPDATE_APPLY] >>
    METIS_TAC []
  )
QED

Theorem birs_eval_exp_IMP_symb_symbols_SUBSET_environ_thm:
  !bsys be sv ty vn.
  (birs_eval_exp be bsys.bsst_environ = SOME (sv,ty)) ==>
  (birs_symb_symbols (bsys with bsst_environ := birs_update_env (vn,sv) bsys.bsst_environ) SUBSET
   birs_symb_symbols bsys)
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC birs_eval_exp_IMP_vars_of_env_SUBSET_thm >>

  SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_def] >>

  FULL_SIMP_TAC (std_ss) [birs_vars_of_env_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  METIS_TAC [SUBSET_DEF, IN_UNION]
QED


Theorem birs_exec_stmt_jmp_NO_FRESH_SYMBS:
  !prog bsys l.
  birs_freesymbs_EMPTY bsys (birs_exec_stmt_jmp prog l bsys)
Proof
SIMP_TAC std_ss [birs_exec_stmt_jmp_def] >>
    REPEAT STRIP_TAC >>

    CASE_TAC >> (
      SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, FORALL_IN_IMAGE] >>
      REPEAT STRIP_TAC >>

      MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_exec_stmt_jmp_to_label_def] >>
      TRY CASE_TAC >> (
        SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
      )
    )
QED

Theorem birs_exec_stmt_cjmp_NO_FRESH_SYMBS:
  !prog bsys e l1 l2.
  birs_freesymbs_EMPTY bsys (birs_exec_stmt_cjmp prog e l1 l2 bsys)
Proof
SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_cjmp_def] >>
  REPEAT STRIP_TAC >>
  CASE_TAC >- (
    SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `x` >>
  Cases_on `r` >> (
    SIMP_TAC (std_ss++holBACore_ss) [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
    TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `b` >> (
    SIMP_TAC (std_ss++holBACore_ss) [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
    TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  SIMP_TAC std_ss [IN_UNION] >>

  `birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond q) /\
   birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond (BExp_UnaryExp BIExp_Not q))` by (
    REPEAT STRIP_TAC >> (
      MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>
      ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
      METIS_TAC []
    )
  ) >>

  REPEAT STRIP_TAC >> (
    IMP_RES_TAC (REWRITE_RULE [birs_freesymbs_EMPTY_thm] birs_exec_stmt_jmp_NO_FRESH_SYMBS) >>
    METIS_TAC [birs_freesymbs_SING_EMPTY_SUFFICIENT3_thm, SUBSET_REFL]
  )
QED
  

Theorem birs_exec_stmtE_NO_FRESH_SYMBS:
  !prog bsys estmt.
  birs_freesymbs_EMPTY bsys (birs_exec_stmtE prog estmt bsys)
Proof
REPEAT STRIP_TAC >>
  Cases_on `estmt` >- (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_jmp_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_cjmp_NO_FRESH_SYMBS]
  ) >> (
    SIMP_TAC std_ss [birs_exec_stmtE_def, birs_exec_stmt_halt_def] >>
    SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, FORALL_IN_IMAGE] >>
    MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  )
QED

Theorem birs_exec_stmt_assign_NO_FRESH_SYMBS:
  !bsys var be.
  birs_freesymbs_EMPTY bsys (birs_exec_stmt_assign var be bsys)
Proof
SIMP_TAC std_ss [birs_exec_stmt_assign_def] >>
  REPEAT STRIP_TAC >>

  CASE_TAC >- (
    SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
  ) >>

  Cases_on `x` >>
  SIMP_TAC (std_ss++holBACore_ss) [pairTheory.pair_CASE_def] >>

  CASE_TAC >- (
    IMP_RES_TAC birs_eval_exp_IMP_symb_symbols_SUBSET_environ_thm >>
    SIMP_TAC (std_ss++holBACore_ss) [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>

    SIMP_TAC std_ss [birs_freesymbs_SING_EMPTY_def, birs_freesymbs_SING_def] >>
    METIS_TAC [SUBSET_DIFF_EMPTY]
  ) >>

  SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
  TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
  SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
QED

Theorem birs_exec_stmt_assert_assume_NO_FRESH_SYMBS:
  !bsys be.
  birs_freesymbs_EMPTY bsys (birs_exec_stmt_assert be bsys) /\
  birs_freesymbs_EMPTY bsys (birs_exec_stmt_assume be bsys)
Proof
SIMP_TAC std_ss [birs_exec_stmt_assert_def, birs_exec_stmt_assume_def] >>
  REPEAT STRIP_TAC >> (
    CASE_TAC >- (
      SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
      TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    Cases_on `x` >>
    Cases_on `r` >> (
      SIMP_TAC (std_ss++holBACore_ss) [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
      TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    Cases_on `b` >> (
      SIMP_TAC (std_ss++holBACore_ss) [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY, pairTheory.pair_CASE_def] >>
      TRY (MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm) >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    `birs_symb_symbols bsys = birs_symb_symbols (bsys with bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond q) /\
     !status. birs_symb_symbols bsys = birs_symb_symbols (bsys with <|bsst_status := status;
             bsst_pcond := BExp_BinExp BIExp_And bsys.bsst_pcond (BExp_UnaryExp BIExp_Not q)|>)` by (
      REPEAT STRIP_TAC >- (
        MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_thm >>
        ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
        METIS_TAC []
      ) >>

      MATCH_MP_TAC birs_eval_exp_IMP_symb_symbols_EQ_pcond_status_thm >>
      ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
      METIS_TAC []
    ) >>

    REPEAT STRIP_TAC >> (
      ASM_SIMP_TAC std_ss [birs_freesymbs_SING_EMPTY_def, birs_freesymbs_SING_def] >>
      METIS_TAC [DIFF_EQ_EMPTY]
    )
  )
QED

Theorem birs_exec_stmtB_NO_FRESH_SYMBS:
  !bsys stmt.
  birs_freesymbs_EMPTY bsys (birs_exec_stmtB stmt bsys)
Proof
REPEAT STRIP_TAC >>
  Cases_on `stmt` >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assign_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assert_assume_NO_FRESH_SYMBS]
  ) >- (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_assert_assume_NO_FRESH_SYMBS]
  ) >> (
    SIMP_TAC std_ss [birs_exec_stmtB_def, birs_exec_stmt_observe_def, LET_DEF] >>
    CASE_TAC >- (
      SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
      MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm >>
      SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
    ) >>

    CASE_TAC >>
    CASE_TAC >> (
      TRY CASE_TAC >> (
        TRY CASE_TAC >> (
          SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
          MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm >>
          SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_typeerror_def]
        )
      )
    )
  )
QED

Theorem birs_exec_step_NO_FRESH_SYMBS[local]:
  !prog bsys.
(*
  (* this assumption is only needed because of the proof with the soundness of steps *)
  (bir_prog_has_no_halt prog) ==>
*)
  birs_freesymbs_EMPTY bsys (birs_exec_step prog bsys)
Proof
SIMP_TAC std_ss [birs_exec_step_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `birs_state_is_terminated bsys` >- (
    ASM_SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    METIS_TAC [birs_freesymbs_SING_EMPTY_SUFFICIENT_thm]
  ) >>

  ASM_SIMP_TAC std_ss [] >>
  Cases_on `bir_get_current_statement prog bsys.bsst_pc` >- (
    ASM_SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_INSERT, NOT_IN_EMPTY] >>
    MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT_thm >>
    SIMP_TAC (std_ss++birs_state_ss) [birs_state_set_failed_def]
  ) >>

  ASM_SIMP_TAC std_ss [] >>
  REPEAT (POP_ASSUM (K ALL_TAC)) >>
  Cases_on `x` >> (
    ASM_SIMP_TAC std_ss [birs_exec_stmt_def, LET_DEF, birs_exec_stmtE_NO_FRESH_SYMBS]
  ) >>

  SIMP_TAC std_ss [birs_freesymbs_EMPTY_thm, FORALL_IN_IMAGE] >>
  REPEAT STRIP_TAC >>
  ASSUME_TAC (Q.SPECL [`bsys`, `b`] birs_exec_stmtB_NO_FRESH_SYMBS) >>
  IMP_RES_TAC birs_freesymbs_EMPTY_thm >>

  Cases_on `birs_state_is_terminated st'` >> (
    ASM_SIMP_TAC std_ss []
  ) >>

  MATCH_MP_TAC birs_freesymbs_SING_EMPTY_SUFFICIENT2_thm >>
  SIMP_TAC (std_ss++birs_state_ss) [] >>
  METIS_TAC []
QED


(* ******************************************************* *)
(*      STEP SEQ rule                                      *)
(* ******************************************************* *)
Theorem birs_rule_STEP_SEQ_gen_thm:
  !prog bs1 L bs2.
  (bir_prog_has_no_halt prog) ==>

  (birs_symb_exec prog
    (bs1,
     L,
     {bs2}
  )) ==>

  (birs_symb_exec prog
    (bs1,
     (bs2.bsst_pc) INSERT L,
     (birs_exec_step prog bs2)
  ))
Proof
  REWRITE_TAC [birs_symb_exec_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPECL [`prog`, `bs2`] birs_rule_STEP_gen2_thm) >>
  REV_FULL_SIMP_TAC std_ss [birs_symb_exec_def] >>

  ASSUME_TAC (Q.SPEC `prog` bir_symb_soundTheory.birs_symb_symbols_f_sound_thm) >>
  IMP_RES_TAC (REWRITE_RULE [symb_freesymbs_def] symb_rulesTheory.symb_rule_SEQ_thm) >>
  POP_ASSUM (ASSUME_TAC o Q.SPECL [`birs_symb_to_symbst bs2`, `birs_symb_to_symbst bs1`, `IMAGE birs_symb_to_symbst (birs_exec_step prog bs2)`]) >>
  ASSUME_TAC (REWRITE_RULE [birs_freesymbs_EMPTY_def, birs_freesymbs_thm] birs_exec_step_NO_FRESH_SYMBS) >>
  FULL_SIMP_TAC std_ss [INTER_EMPTY,
    birs_auxTheory.birs_symb_symbols_set_EQ_thm, bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm] >>

  `L UNION {bs2.bsst_pc} = bs2.bsst_pc INSERT L` by (
    METIS_TAC [INSERT_UNION_EQ, UNION_EMPTY, UNION_COMM]
  ) >>

  `(IMAGE birs_symb_to_symbst {bs2} DIFF {birs_symb_to_symbst bs2}) UNION
               IMAGE birs_symb_to_symbst (birs_exec_step prog bs2)
   = IMAGE birs_symb_to_symbst (birs_exec_step prog bs2)` by (
    SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, DIFF_EQ_EMPTY, UNION_EMPTY]
  ) >>

  METIS_TAC []
QED

(*
bir_symbTheory.birs_state_t_bsst_pc
bir_symbTheory.birs_state_t_accfupds
*)

(*
val bprog_tm = ``
BirProgram [] : 'obs_type bir_program_t
``;
Theorem no_halt_thm[local]:
  bir_prog_has_no_halt (^bprog_tm)
Proof
cheat
QED
*)



(* ******************************************************* *)
(*      jump resolution - birs_symbval_concretizations     *)
(* ******************************************************* *)

local
  open bir_bool_expTheory
in

Theorem birs_jumptarget_singletonconst_thm:
!pcond vaex iv.
  (!i. birs_interpret_fun i vaex = SOME (BVal_Imm iv)) ==>
  (?i. birs_interpret_fun i pcond = SOME bir_val_true) ==>
  (birs_symbval_concretizations pcond vaex = {BL_Address iv})
Proof
  rpt strip_tac >>
  rw [birs_symbval_concretizations_def] >>
  fs [EXTENSION] >>
  METIS_TAC []
QED

Theorem birs_jumptarget_empty_thm:
!pcond vaex iv.
  (!i. birs_interpret_fun i pcond = SOME bir_val_false) ==>
  (birs_symbval_concretizations pcond vaex = EMPTY)
Proof
  rpt strip_tac >>
  rw [birs_symbval_concretizations_def] >>
  simp_tac (std_ss++holBACore_ss++wordsLib.WORD_ss++pred_setSimps.GSPEC_SIMP_ss) [bir_val_true_def, bir_val_false_def]
QED

end;

val _ = export_theory();
