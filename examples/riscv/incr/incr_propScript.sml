open HolKernel boolLib Parse bossLib;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open tutorial_smtSupportLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open incrTheory;

open incr_symb_execTheory;

val _ = new_theory "incr_prop";

(* ------ *)

Definition riscv_incr_pre_def:
 riscv_incr_pre (m : riscv_state) = T (* FIXME *)
End

Definition riscv_incr_post_def:
 riscv_incr_post (m : riscv_state) = T (* FIXME *)
End

Definition bir_incr_pre_def:
  bir_incr_pre x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bir_incr_post_def:
 bir_incr_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (x + 1w)))
End

(* ------ *)

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) incr_symb_analysis_thm;

Definition incr_analysis_L_def:
 incr_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 4w))``;

Definition bprecond_def:
  bprecond = bir_incr_pre
End

val bprecond = (fst o dest_eq o concl) bprecond_def;

Definition bsysprecond_def:
  bsysprecond x = FST (THE (birs_eval_exp (^bprecond x) (bir_senv_GEN_list birenvtyl_riscv)))
End

Theorem bprecond_birs_eval_exp_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC
   birs_stepLib.birs_eval_exp_CONV)
     ``birs_eval_exp (bprecond x) (bir_senv_GEN_list birenvtyl_riscv)``

Theorem bsysprecond_thm =
 (REWRITE_CONV [bsysprecond_def, birs_eval_exp_ALT_thm, bprecond_birs_eval_exp_thm] THENC EVAL) ``bsysprecond x``

Theorem bprecond_birs_eval_exp_thm2 = REWRITE_CONV [bprecond_birs_eval_exp_thm, GSYM bsysprecond_thm] ``birs_eval_exp (bprecond x) (bir_senv_GEN_list birenvtyl_riscv)``

val bsysprecond = (fst o dest_eq o concl o Q.SPEC `pre_x10`) bsysprecond_def;

val birs_state_init_pre = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl_riscv;
  bsst_status   := BST_Running;
  bsst_pcond    := ^bsysprecond
|>``;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
val birs_state_init_pre_EQ_thm =
 REWRITE_RULE [] ((REWRITE_CONV [bsysprecond_thm] THENC
  SIMP_CONV (std_ss++birs_state_ss++holBACore_ss) [] THENC
  EVAL)
  ``^((snd o dest_comb) sys_i) = ^birs_state_init_pre``);

val incr_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm] incr_symb_analysis_thm;

Theorem birenvtyl_riscv_EVAL_thm =
 (REWRITE_CONV [birenvtyl_riscv_def, riscv_vars_def,
   bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
   bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL) ``birenvtyl_riscv``

val birs_state_thm = REWRITE_CONV [birenvtyl_riscv_EVAL_thm] birs_state_init_pre;

(* ------ *)

(* now the transfer *)

val bprog_tm = (fst o dest_eq o concl) bir_incr_prog_def;

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);

Definition bprog_P_def:
  bprog_P x ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       pc.bpc_index = 0 /\
       bir_envty_list birenvtyl_riscv st /\
       bir_eval_exp (^bprecond x) (BEnv st) = SOME bir_val_true)
End

(* translate the property to BIR state property *)
Theorem bprog_P_thm:
  !x bs.
  bprog_P x (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bs.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl_riscv bs.bst_environ /\
       bir_eval_exp (^bprecond x) bs.bst_environ = SOME bir_val_true)
Proof
 REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_P_def, bir_envty_list_b_thm, bir_BEnv_lookup_EQ_thm]
QED

Definition bprog_Q_def:
  bprog_Q x
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (
       (pc2 = ^birs_state_end_lbl)
       /\
       (status2 = BST_Running)
       /\
       (st2 "x10" = SOME (BVal_Imm (Imm64 (x + 1w))))
     )
End

Theorem bprog_Q_thm:
  !x bs1 bs2.
  bprog_Q x (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = ^birs_state_end_lbl)
      /\
      (bs2.bst_status = BST_Running)
      /\
      (bir_env_lookup "x10" bs2.bst_environ = SOME (BVal_Imm (Imm64 (x + 1w))))
    )
Proof
FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
QED
(* ........................... *)

(* P is generic enough *)

Theorem bprog_P_entails_thm:
  P_entails_an_interpret (bir_symb_rec_sbir ^bprog_tm) (bprog_P pre_x10) (birs_symb_to_symbst ^birs_state_init_pre)
Proof
FULL_SIMP_TAC (std_ss++birs_state_ss) [P_entails_an_interpret_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_EQ_thm] >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_to_symbst_def, symb_symbst_pc_def] >>

  Cases_on `s` >> Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_typesLib.symb_TYPES_ss) [bprog_P_def, birs_symb_to_concst_def, symb_concst_pc_def] >>

  Cases_on `b0` >>
  FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_env_lookup_def] >>
  PAT_X_ASSUM ``A = (\B. C)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss) [boolTheory.ETA_THM] >>

  `(ALL_DISTINCT (MAP FST birenvtyl_riscv))` by EVAL_TAC >>

  METIS_TAC [bprog_P_entails_gen_thm, birenvtyl_EVAL_thm, bprecond_birs_eval_exp_thm2]
QED

(* ........................... *)


Theorem bir_Pi_overapprox_Q_thm:
  !p P sys Pi Q.
  (Pi_overapprox_Q (bir_symb_rec_sbir p) P (birs_symb_to_symbst sys) (IMAGE birs_symb_to_symbst Pi) Q)
  <=>
  (!sys2 bs bs' H.
     sys2 IN Pi ==>
     birs_symb_matchstate sys H bs ==>
     (\bs. P (birs_symb_to_concst bs)) bs ==>
     (?H'. symb_interpr_ext H' H /\ birs_symb_matchstate sys2 H' bs') ==>
     (\bs bs'. Q (birs_symb_to_concst bs) (birs_symb_to_concst bs')) bs bs')
Proof
FULL_SIMP_TAC (std_ss++birs_state_ss) [Pi_overapprox_Q_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>

  EQ_TAC >- (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`birs_symb_to_symbst sys2`, `birs_symb_to_concst bs`, `birs_symb_to_concst bs'`, `H`]) >>

    REV_FULL_SIMP_TAC (std_ss) [IMAGE_IN, symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
    METIS_TAC []
  ) >>

  REPEAT STRIP_TAC >>

  `?bsys. sys' = birs_symb_to_symbst bsys` by (
    METIS_TAC [birs_symb_to_symbst_EXISTS_thm]
  ) >>
  `?bs.  s  = birs_symb_to_concst bs /\
   ?bs'. s' = birs_symb_to_concst bs'` by (
    METIS_TAC [birs_symb_to_concst_EXISTS_thm]
  ) >>

  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`bsys`, `bs`, `bs'`, `H`]) >>

  `bsys IN Pi` by (
    FULL_SIMP_TAC std_ss [] >>

    `birs_symb_from_symbst o birs_symb_to_symbst = I` by (
      SIMP_TAC std_ss [combinTheory.o_DEF, bir_symbTheory.birs_symb_to_from_symbst_thm] >>
      MATCH_MP_TAC boolTheory.EQ_EXT >>
      SIMP_TAC std_ss [combinTheory.I_THM]
    ) >>
    METIS_TAC [IMAGE_IN, IMAGE_IMAGE, bir_symbTheory.birs_symb_to_from_symbst_thm, IMAGE_I]
  ) >>

  FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
  REV_FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>
  METIS_TAC []
QED


(* Q is implied by sys and Pi *)
Theorem bprog_Pi_overapprox_Q_thm:
  Pi_overapprox_Q (bir_symb_rec_sbir ^bprog_tm) (bprog_P pre_x10) (birs_symb_to_symbst ^birs_state_init_pre) ^Pi_f(*(IMAGE birs_symb_to_symbst {a;b;c;d})*) (bprog_Q pre_x10)
Proof
REWRITE_TAC [bir_Pi_overapprox_Q_thm] >>
  REPEAT GEN_TAC >>

  REWRITE_TAC [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  STRIP_TAC >> (
    POP_ASSUM (fn thm => (ASSUME_TAC thm >> Q.ABBREV_TAC `sys3 = ^((snd o dest_eq o concl) thm)`)) >>
    ASM_SIMP_TAC std_ss [] >>
    rename1 `sys4 = sys3` >>
    rename1 `sys4 = sys2` >>
    PAT_X_ASSUM ``A = B`` (K ALL_TAC) >>

    DISCH_TAC >>
    POP_ASSUM (fn thm => (ASSUME_TAC thm >> Q.ABBREV_TAC `sys1 = ^((snd o dest_comb o fst o dest_comb o fst o dest_comb o concl) thm)`)) >>
    POP_ASSUM (fn thm0 => POP_ASSUM (fn thm1 => (ASSUME_TAC thm0 >> ASSUME_TAC thm1))) >>
    REPEAT STRIP_TAC >>

    (* now the proof state is somewhat clean *)

    FULL_SIMP_TAC (std_ss) [bprog_Q_thm] >>
    (* pc *)
    CONJ_TAC >- (
      Q.UNABBREV_TAC `sys2` >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>
    (* status Running *)
    CONJ_TAC >- (
      Q.UNABBREV_TAC `sys2` >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>

    (* the property (here: pre_x10 + 1) *)
    `BVar "sy_x10" (BType_Imm Bit64) IN symb_interpr_dom H` by (
      `symb_interpr_for_symbs (birs_symb_symbols sys1) H` by (
        FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
      ) >>

      Q.UNABBREV_TAC `sys1` >>
      POP_ASSUM (ASSUME_TAC o CONV_RULE (
          REWRITE_CONV [bsysprecond_thm, birenvtyl_EVAL_thm] THENC
          computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC
          aux_setLib.birs_symb_symbols_MATCH_CONV)
        ) >>

      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>
    `BVar "sy_x10" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
      `symb_interpr_for_symbs (birs_symb_symbols sys2) H'` by (
        FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
      ) >>

      Q.UNABBREV_TAC `sys2` >>
      POP_ASSUM (ASSUME_TAC o CONV_RULE (
          REWRITE_CONV [bsysprecond_thm, birenvtyl_EVAL_thm] THENC
          computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC
          aux_setLib.birs_symb_symbols_MATCH_CONV)
        ) >>

      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>

    `symb_interpr_get H' (BVar "sy_x10" (BType_Imm Bit64)) = symb_interpr_get H (BVar "sy_x10" (BType_Imm Bit64))` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def]
    ) >>

    `bir_eval_exp (bprecond pre_x10) bs.bst_environ = SOME bir_val_true` by (
      Q.UNABBREV_TAC `sys1` >>
      FULL_SIMP_TAC (std_ss) [bprog_P_thm]
    ) >>

    (* use bprog_P *)
    `symb_interpr_get H (BVar "sy_x10" (BType_Imm Bit64)) = SOME (BVal_Imm (Imm64 pre_x10))` by (
      FULL_SIMP_TAC (std_ss) [bprog_P_thm] >>
      `bir_env_lookup "x10" bs.bst_environ = SOME (BVal_Imm (Imm64 pre_x10))` by (
        cheat
      ) >>

      cheat
(*
      Q.UNABBREV_TAC `sys1` >>
      Q.UNABBREV_TAC `sys2` >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"x10"`)) >>
      FULL_SIMP_TAC (std_ss) [] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_interpr_welltyped_def] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `BVar "sy_x10" (BType_Imm Bit64)`)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

      Cases_on `symb_interpr_get H (BVar "sy_x10" (BType_Imm Bit64))` >- (
        METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, optionTheory.option_CLAUSES]
      ) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES] >>

      `bir_val_is_Imm_s Bit64 x` by (
        METIS_TAC [bir_valuesTheory.bir_val_checker_TO_type_of]
      ) >>
      FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_is_Imm_s_def, bir_immTheory.n2bs_def] >>

      FULL_SIMP_TAC (std_ss++holBACore_ss) []
*)
    ) >>

    (* *)
    cheat
(*
    `(?v.
       bir_env_lookup "countw" bs.bst_environ = SOME v /\
       birs_interpret_fun H (THE (sys1.bsst_environ "countw")) = SOME v) /\
     (?v'.
       bir_env_lookup "countw" bs'.bst_environ = SOME v' /\
       birs_interpret_fun H' (THE (sys2.bsst_environ "countw")) = SOME v')` by (
      Q.UNABBREV_TAC `sys1` >>
      Q.UNABBREV_TAC `sys2` >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"countw"`)) >>
      FULL_SIMP_TAC (std_ss) [] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_interpr_welltyped_def] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `BVar "sy_countw" (BType_Imm Bit64)`)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

      Cases_on `symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` >- (
        METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, optionTheory.option_CLAUSES]
      ) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES] >>

      FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_auxTheory.birs_gen_env_GET_thm, birs_auxTheory.birs_gen_env_GET_NULL_thm] >>
      ASM_REWRITE_TAC [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def, bir_typing_expTheory.bir_vars_of_exp_def, bir_envTheory.bir_env_empty_def, bir_envTheory.bir_env_map_empty_def] >>

      computeLib.RESTR_EVAL_TAC [``bir_exp_subst``] >>
      ASM_REWRITE_TAC []
    ) >>

    REPEAT (PAT_X_ASSUM ``birs_symb_matchstate A B C`` (K ALL_TAC)) >>
    Q.UNABBREV_TAC `sys1` >>
    Q.UNABBREV_TAC `sys2` >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_auxTheory.birs_gen_env_GET_thm, birs_auxTheory.birs_gen_env_GET_NULL_thm] >>
    (* now the proof state is pretty much cleaned up *)

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm] >>
    REPEAT (PAT_X_ASSUM ``birs_interpret_fun_ALT A B = SOME C`` (ASSUME_TAC o computeLib.RESTR_EVAL_RULE [])) >>
    FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    PAT_X_ASSUM ``BVal_Imm (Imm64 A) = B`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    (* still have to unpack the precondition for the space fact about countw *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bprecond_def] >>
    REPEAT (PAT_X_ASSUM ``bir_eval_bin_exp BIExp_And A B = SOME bir_val_true`` (ASSUME_TAC o MATCH_MP birs_rulesTheory.bir_conj_true) >> FULL_SIMP_TAC std_ss []) >>
    IMP_RES_TAC bir_env_read_countw_lookup_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_bool_expTheory.bir_val_TF_bool2b_DEF] >>
    PAT_X_ASSUM ``v1 <=+ A`` (MP_TAC) >>
    REPEAT (POP_ASSUM (K ALL_TAC)) >>

(*
    now we are only left with the word relation
*)

    HolSmtLib.Z3_ORACLE_TAC
*)
  )
QED
(* ........................... *)





Theorem abstract_jgmt_rel_incr[local]:
 abstract_jgmt_rel (bir_ts bir_incr_prog) (BL_Address (Imm64 0w)) {BL_Address (Imm64 4w)}
  (\st. bir_exec_to_labels_triple_precond st (bir_incr_pre pre_x10) bir_incr_prog)
  (\st st'. bir_exec_to_labels_triple_postcond st' (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false) bir_incr_prog)
Proof
 (* reasoning via symb_prop_transfer_thm goes here *)
 cheat
QED

Theorem bir_cont_incr[local]:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_incr_pre pre_x10)
  (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false)
Proof
 `{BL_Address (Imm64 4w)} <> {}` by fs [] >>
 MP_TAC (Q.SPECL [`bir_incr_prog`,
  `BL_Address (Imm64 0w)`,
  `{BL_Address (Imm64 4w)}`,
  `bir_incr_pre pre_x10`,
  `\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false`
 ] abstract_jgmt_rel_bir_cont) >>
 rw [] >>
 METIS_TAC [abstract_jgmt_rel_incr]
QED

(* TODO: RISC-V backlifting *)

val _ = export_theory ();
