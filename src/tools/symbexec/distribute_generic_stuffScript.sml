open HolKernel boolLib Parse bossLib;

open finite_mapTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_typing_expTheory;
open bir_htTheory;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
(*open birs_stepLib;*)
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "distribute_generic_stuff";

(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)
Definition P_bircont_def:
  P_bircont envtyl bpre ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       pc.bpc_index = 0 /\ (* we need this for bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_thm *)
       bir_envty_list envtyl st /\
       bir_eval_exp bpre (BEnv st) = SOME bir_val_true)
End

Definition Q_bircont_def:
  Q_bircont end_lbl vars bpost
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (
       (pc2 = end_lbl)
       /\
       (status2 = BST_Running)
       /\
       (bir_env_vars_are_initialised (BEnv st2) (vars)) /\
       (bir_eval_exp bpost (BEnv st2) = SOME bir_val_true)
     )
End

(* translate the property to BIR state property *)

Theorem P_bircont_thm:
  !envtyl bpre bs.
  P_bircont envtyl bpre (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bs.bst_pc.bpc_index = 0 /\
       bir_envty_list_b envtyl bs.bst_environ /\
       bir_eval_exp bpre bs.bst_environ = SOME bir_val_true)
Proof
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, P_bircont_def, bir_envty_list_b_thm, bir_BEnv_lookup_EQ_thm]
QED

Theorem Q_bircont_thm:
  !end_lbl vars bpost bs1 bs2.
  Q_bircont end_lbl vars bpost (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = end_lbl)
      /\
      (bs2.bst_status = BST_Running)
      /\
      (bir_env_vars_are_initialised bs2.bst_environ (vars))
      /\
      (bir_eval_exp bpost bs2.bst_environ = SOME bir_val_true)
    )
Proof
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, Q_bircont_def, bir_BEnv_lookup_EQ_thm]
QED

Definition pre_bircont_nL_def:
  pre_bircont_nL envtyl bpre st =
      (
       st.bst_status = BST_Running /\
       st.bst_pc.bpc_index = 0 /\
       bir_envty_list_b envtyl st.bst_environ /\

       bir_eval_exp bpre st.bst_environ = SOME bir_val_true
      )
End

Definition post_bircont_nL_def:
  post_bircont_nL end_lbl vars bpost (st:bir_state_t) st' =
      (
         (st'.bst_pc = end_lbl) /\
         st'.bst_status = BST_Running /\
         bir_env_vars_are_initialised st'.bst_environ vars /\

         bir_eval_exp bpost st'.bst_environ = SOME bir_val_true
      )
End

Theorem P_bircont_pre_nL_thm:
  !envtyl bpre bs.
  P_bircont envtyl bpre (birs_symb_to_concst bs) = pre_bircont_nL envtyl bpre bs
Proof
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [P_bircont_thm, pre_bircont_nL_def]
QED

Theorem Q_bircont_post_nL_thm:
  !end_lbl vars bpost bs1 bs2.
  Q_bircont end_lbl vars bpost (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) = post_bircont_nL end_lbl vars bpost bs1 bs2
Proof
  FULL_SIMP_TAC (std_ss) [Q_bircont_thm, post_bircont_nL_def]
QED



Definition birs_state_init_pre_GEN_def:
  birs_state_init_pre_GEN start_lbl birenvtyl bsysprecond =
    <|
      bsst_pc       := start_lbl;
      bsst_environ  := bir_senv_GEN_list birenvtyl;
      bsst_status   := BST_Running;
      bsst_pcond    := bsysprecond
    |>
End

Definition mk_bsysprecond_def:
  mk_bsysprecond bpre envtyl = FST (THE (birs_eval_exp bpre (bir_senv_GEN_list envtyl)))
End

Theorem bir_envty_includes_birs_envty_of_senv_bir_senv_GEN_list_thm:
  !envtyl.
  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (bir_envty_includes_vs (birs_envty_of_senv (bir_senv_GEN_list envtyl)) (set (MAP PairToBVar envtyl)))
Proof
  REWRITE_TAC [bir_envTheory.bir_envty_includes_vs_def, bir_envTheory.bir_envty_includes_v_def, birs_envty_of_senv_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `v` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [listTheory.MEM_MAP] >>
  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [PairToBVar_def] >>
  IMP_RES_TAC birs_auxTheory.bir_senv_GEN_list_APPLY_thm >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_senv_GEN_bvar_def]
QED

Theorem mk_bsysprecond_thm:
  !bpre envtyl ty.
  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (bir_vars_of_exp bpre SUBSET set (MAP PairToBVar envtyl)) ==>
  (type_of_bir_exp bpre = SOME ty) ==>
  (birs_eval_exp bpre (bir_senv_GEN_list envtyl) = SOME (mk_bsysprecond bpre envtyl,ty))
Proof
  REPEAT STRIP_TAC >>
  `bir_envty_includes_vs (birs_envty_of_senv (bir_senv_GEN_list envtyl)) (bir_vars_of_exp bpre)` by (
    METIS_TAC [bir_envty_includes_birs_envty_of_senv_bir_senv_GEN_list_thm, bir_envTheory.bir_envty_includes_vs_SUBSET]
  ) >>
  IMP_RES_TAC bir_symbTheory.birs_eval_exp_SOME_EQ_bir_exp_env_type_thm >>
  ASM_SIMP_TAC std_ss [mk_bsysprecond_def]
QED

Theorem P_bircont_entails_thm:
  !p envtyl bpre bsyspre start_lbl.
  (bir_vars_of_program p = set (MAP PairToBVar envtyl)) ==>
  (bir_vars_of_exp bpre SUBSET set (MAP PairToBVar envtyl)) ==>
  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (IS_SOME (type_of_bir_exp bpre)) ==>
  (bsyspre = mk_bsysprecond bpre envtyl) ==>
  (P_entails_an_interpret
    (bir_symb_rec_sbir p)
    (P_bircont envtyl bpre)
    (birs_symb_to_symbst (birs_state_init_pre_GEN start_lbl envtyl bsyspre)))
Proof
  FULL_SIMP_TAC (std_ss++birs_state_ss) [P_entails_an_interpret_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_EQ_thm] >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_to_symbst_def, symb_symbst_pc_def, birs_state_init_pre_GEN_def] >>

  Cases_on `s` >> Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_typesLib.symb_TYPES_ss) [P_bircont_def, birs_symb_to_concst_def, symb_concst_pc_def, bir_BEnv_lookup_EQ_thm] >>

  Cases_on `b0` >>
  FULL_SIMP_TAC (std_ss) [bir_env_lookup_I_thm] >>

  `?ty. birs_eval_exp bpre (bir_senv_GEN_list envtyl) = SOME (mk_bsysprecond bpre envtyl,ty)` by (
    METIS_TAC [mk_bsysprecond_thm, optionTheory.IS_SOME_EXISTS]
  ) >>

  METIS_TAC [bprog_P_entails_gen_thm]
QED

Theorem birs_env_vars_are_initialised_IMP_thm:
  !H symbs senv env vs.
    birs_interpr_welltyped H ==>
    symb_interpr_for_symbs symbs H ==>
    birs_matchenv H senv env ==>
    birs_env_vars_are_initialised senv symbs vs ==>
    bir_env_vars_are_initialised env vs
Proof
  REWRITE_TAC [birs_env_vars_are_initialised_def, bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPEC `v`) >>
  REV_FULL_SIMP_TAC std_ss [birs_env_var_is_initialised_def, bir_env_var_is_initialised_def] >>

  FULL_SIMP_TAC std_ss [birs_matchenv_def] >>
  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPEC `bir_var_name v`) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bir_symb_sound_coreTheory.birs_interpret_fun_PRESERVES_type_thm >>
  FULL_SIMP_TAC std_ss []
QED






(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)

(* lift to concrete state property *)
Theorem prop_holds_TO_step_n_in_L_thm:
!p start_lbl exit_lbl L P Q.
  (prop_holds (bir_symb_rec_sbir p)
       start_lbl L P Q) ==>
  (!st.
   (symb_concst_pc (birs_symb_to_concst st) = start_lbl) ==>
   (P (birs_symb_to_concst st)) ==>
   (?n st'.
     (step_n_in_L
       (symb_concst_pc o birs_symb_to_concst)
       (SND o bir_exec_step p)
       st
       n
       L
       st') /\
      (Q (birs_symb_to_concst st) (birs_symb_to_concst st'))))
Proof
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [prop_holds_def] >>
  PAT_X_ASSUM ``!x. A`` IMP_RES_TAC >>
  ASSUME_TAC (Q.SPEC `s'` birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `st'` >>
  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [conc_step_n_in_L_def, bir_symb_rec_sbir_def] >>
  FULL_SIMP_TAC (pure_ss) [] >>
  REV_FULL_SIMP_TAC (pure_ss) [] >>

  FULL_SIMP_TAC (pure_ss) [
    GSYM (SIMP_RULE std_ss [birs_symb_to_from_concst_thm, birs_symb_to_concst_EXISTS_thm, birs_symb_to_concst_EQ_thm] (
      SPECL [``birs_symb_to_concst``, ``birs_symb_from_concst``] (
        INST_TYPE [Type`:'b` |-> Type`:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t`, Type`:'a` |-> Type`:bir_state_t`] step_n_in_L_ABS_thm)
   ))] >>
  FULL_SIMP_TAC (std_ss) []
QED

(* finish translation to pure BIR property *)
Theorem prop_holds_TO_step_n_in_L_BIR_thm:
!p start_lbl exit_lbl L envtyl vars bpre bpost.
  (prop_holds (bir_symb_rec_sbir p)
       start_lbl L (P_bircont envtyl bpre) (Q_bircont exit_lbl vars bpost)) ==>
  (!st.
       st.bst_pc = start_lbl ==>
       pre_bircont_nL envtyl bpre st ==>
       ?n st'.
         step_n_in_L (\x. x.bst_pc) (\x. bir_exec_step_state p x)
           st n L st' /\ post_bircont_nL exit_lbl vars bpost st st')
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC prop_holds_TO_step_n_in_L_thm >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [birs_symb_concst_pc_thm, P_bircont_pre_nL_thm, Q_bircont_post_nL_thm] >>
  PAT_X_ASSUM ``!x. A`` IMP_RES_TAC >>
  FULL_SIMP_TAC std_ss [P_bircont_pre_nL_thm, Q_bircont_post_nL_thm, birs_symb_concst_pc_thm, combinTheory.o_DEF, GSYM bir_programTheory.bir_exec_step_state_def] >>
  METIS_TAC []
QED

Theorem prop_holds_TO_step_n_in_L_BIR_fmap_thm[local]:
!p start_lbl L envtyl vars bpre fm.
  (prop_holds (bir_symb_rec_sbir p)
    start_lbl L (P_bircont envtyl bpre)
    (\st st'. ITFMAP (\exit_albl bpost Qs. Qs \/ Q_bircont exit_albl vars bpost st st') fm F)) ==>
  (!st.
       st.bst_pc = start_lbl ==>
       pre_bircont_nL envtyl bpre st ==>
       ?n st'.
         step_n_in_L (\x. x.bst_pc) (\x. bir_exec_step_state p x)
           st n L st' /\
           (ITFMAP (\exit_albl bpost pLs. pLs \/ post_bircont_nL exit_albl vars bpost st st') fm F))
Proof
 cheat
QED

Theorem prop_holds_TO_step_n_in_L_BIR_two_thm:
!p start_lbl exit_lbl_1 exit_lbl_2 L envtyl vars bpre bpost_1 bpost_2.
  (prop_holds (bir_symb_rec_sbir p)
    start_lbl L (P_bircont envtyl bpre) 
    (\st st'. Q_bircont exit_lbl_1 vars bpost_1 st st' \/ Q_bircont exit_lbl_2 vars bpost_2 st st')) ==>
  (!st.
       st.bst_pc = start_lbl ==>
       pre_bircont_nL envtyl bpre st ==>
       ?n st'.
         step_n_in_L (\x. x.bst_pc) (\x. bir_exec_step_state p x)
           st n L st' /\
           (post_bircont_nL exit_lbl_1 vars bpost_1 st st' \/ post_bircont_nL exit_lbl_2 vars bpost_2 st st'))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC prop_holds_TO_step_n_in_L_thm >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [birs_symb_concst_pc_thm, P_bircont_pre_nL_thm, Q_bircont_post_nL_thm] >>
  PAT_X_ASSUM ``!x. A`` IMP_RES_TAC >>
  FULL_SIMP_TAC std_ss [P_bircont_pre_nL_thm, Q_bircont_post_nL_thm, birs_symb_concst_pc_thm, combinTheory.o_DEF, GSYM bir_programTheory.bir_exec_step_state_def] >>
  METIS_TAC []
QED

Theorem prop_holds_TO_bir_step_n_in_L_jgmt_fmap_thm[local]:
!p start_lbl L envtyl vars bpre fm.
  (prop_holds (bir_symb_rec_sbir p)
       start_lbl L (P_bircont envtyl bpre)
   (\st st'. ITFMAP (\exit_albl bpost Qs. Qs \/ Q_bircont exit_albl vars bpost st st') fm F)) ==>
  (bir_step_n_in_L_jgmt
    p
    start_lbl
    L
    (pre_bircont_nL envtyl bpre)
     (\st st'. ITFMAP (\exit_albl bpost pLs. pLs \/ post_bircont_nL exit_albl vars bpost st st') fm F))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC prop_holds_TO_step_n_in_L_BIR_fmap_thm >>

  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  METIS_TAC []
QED

Theorem prop_holds_TO_bir_step_n_in_L_jgmt_thm:
!p start_lbl exit_lbl L envtyl vars bpre bpost.
  (prop_holds (bir_symb_rec_sbir p)
       start_lbl L (P_bircont envtyl bpre) (Q_bircont exit_lbl vars bpost)) ==>
  (bir_step_n_in_L_jgmt
    p
    start_lbl
    L
    (pre_bircont_nL envtyl bpre)
    (post_bircont_nL exit_lbl vars bpost))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC prop_holds_TO_step_n_in_L_BIR_thm >>

  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  METIS_TAC []
QED

Theorem prop_holds_TO_bir_step_n_in_L_jgmt_two_thm:
!p start_lbl exit_lbl_1 exit_lbl_2 L envtyl vars bpre bpost_1 bpost_2.
  (prop_holds (bir_symb_rec_sbir p)
       start_lbl L (P_bircont envtyl bpre)
   (\st st'. Q_bircont exit_lbl_1 vars bpost_1 st st' \/ Q_bircont exit_lbl_2 vars bpost_2 st st')) ==>
  (bir_step_n_in_L_jgmt
    p
    start_lbl
    L
    (pre_bircont_nL envtyl bpre)
    (\st st'. post_bircont_nL exit_lbl_1 vars bpost_1 st st' \/ post_bircont_nL exit_lbl_2 vars bpost_2 st st'))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC prop_holds_TO_step_n_in_L_BIR_two_thm >>

  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  METIS_TAC []
QED

(* use the reasoning on label sets to get to abstract_jgmt_rel for fmap *)
Theorem bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_fmap_thm[local]:
!p start_albl L envtyl vars bpre fm.
  (IMAGE (\exit_albl. <|bpc_label := BL_Address exit_albl; bpc_index := 0|>) (FDOM fm)) INTER L = {} ==>
  (bir_step_n_in_L_jgmt
    p
    <|bpc_label := BL_Address start_albl; bpc_index := 0|>
    L
    (pre_bircont_nL envtyl bpre)
    (\st st'.
      ITFMAP (\exit_albl bpost pLs. pLs \/ post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost st st') fm F)) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    (IMAGE (\exit_albl. BL_Address exit_albl) (FDOM fm))
    (pre_bircont_nL envtyl bpre)
    (\st st'. ITFMAP (\exit_albl bpost pLs. pLs \/ post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost st st') fm F))
Proof
  cheat
QED

(* use the reasoning on label sets to get to abstract_jgmt_rel *)
Theorem bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_thm:
!p start_albl exit_albl L envtyl vars bpre bpost.
  (<|bpc_label := BL_Address exit_albl; bpc_index := 0|> NOTIN L) ==>
  (bir_step_n_in_L_jgmt
    p
    <|bpc_label := BL_Address start_albl; bpc_index := 0|>
    L
    (pre_bircont_nL envtyl bpre)
    (post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost)) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl}
    (pre_bircont_nL envtyl bpre)
    (post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost))
Proof
  REPEAT STRIP_TAC >>

  IMP_RES_TAC (
    (REWRITE_RULE
       [bir_programTheory.bir_block_pc_def]
       bir_program_transfTheory.bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm)) >>

  FULL_SIMP_TAC std_ss [pre_bircont_nL_def] >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `{BL_Address exit_albl}`) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [IMAGE_SING, IN_SING, bir_programTheory.bir_block_pc_def] >>
  `L INTER {<|bpc_label := BL_Address exit_albl; bpc_index := 0|>} = EMPTY` by (
    REWRITE_TAC [GSYM DISJOINT_DEF, IN_DISJOINT] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [IN_SING]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [post_bircont_nL_def, IN_SING]
QED

(* use the reasoning on label sets to get to abstract_jgmt_rel for two *)
Theorem bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_two_thm:
!p start_albl exit_albl_1 exit_albl_2 L envtyl vars bpre bpost_1 bpost_2.
  (<|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> NOTIN L) ==>
  (<|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> NOTIN L) ==>
  (bir_step_n_in_L_jgmt
    p
    <|bpc_label := BL_Address start_albl; bpc_index := 0|>
    L
    (pre_bircont_nL envtyl bpre)
    (\st st'. 
      post_bircont_nL <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st')) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl_1; BL_Address exit_albl_2}
    (pre_bircont_nL envtyl bpre)
    (\st st'. 
      post_bircont_nL <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st'))
Proof
  REPEAT STRIP_TAC >>

  IMP_RES_TAC (
    (REWRITE_RULE
       [bir_programTheory.bir_block_pc_def]
       bir_program_transfTheory.bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm)) >>

  FULL_SIMP_TAC std_ss [pre_bircont_nL_def] >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `{BL_Address exit_albl_1; BL_Address exit_albl_2}`) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [IMAGE_SING, IN_SING, bir_programTheory.bir_block_pc_def] >>
  sg `L INTER {<|bpc_label := BL_Address exit_albl_1; bpc_index := 0|>; <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|>} = {}` >-
   (REWRITE_TAC [GSYM DISJOINT_DEF, IN_DISJOINT] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >> rw [] >> fs []) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [IMAGE_DEF,bir_block_pc_def] >>

  `!st st'. post_bircont_nL
     <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st' ==>
    ?x. st'.bst_pc = <|bpc_label := x; bpc_index := 0|> /\ (x = BL_Address exit_albl_1 ∨ x = BL_Address exit_albl_2)`
   by METIS_TAC [post_bircont_nL_def] >>
  `!st st'. post_bircont_nL
    <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
   post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st' ==>
    ~bir_state_is_terminated st'` by (METIS_TAC [post_bircont_nL_def,bir_state_is_terminated_def]) >>
  METIS_TAC []
QED

(* overall symbolic execution to BIR abstract_jgmt_rel *)
Theorem prop_holds_TO_abstract_jgmt_rel_fmap_thm[local]:
!p start_albl L envtyl vars bpre fm.
  (IMAGE (\exit_albl. <|bpc_label := BL_Address exit_albl; bpc_index := 0|>) (FDOM fm)) INTER L = {} ==>
  (prop_holds (bir_symb_rec_sbir p)
       <|bpc_label := BL_Address start_albl; bpc_index := 0|>
       L
       (P_bircont envtyl bpre)
       (\st st'. ITFMAP (\exit_albl bpost Qs. Qs \/ Q_bircont <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost st st') fm F)) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    (IMAGE (\exit_albl. BL_Address exit_albl) (FDOM fm))
    (pre_bircont_nL envtyl bpre)
    (\st st'.
      ITFMAP (\exit_albl bpost pLs. pLs \/ post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost st st') fm F))
Proof
  cheat
QED

(* overall symbolic execution to BIR abstract_jgmt_rel *)
Theorem prop_holds_TO_abstract_jgmt_rel_thm:
!p start_albl exit_albl L envtyl vars bpre bpost.
  (<|bpc_label := BL_Address exit_albl; bpc_index := 0|> NOTIN L) ==>
  (prop_holds (bir_symb_rec_sbir p)
       <|bpc_label := BL_Address start_albl; bpc_index := 0|>
       L
       (P_bircont envtyl bpre)
       (Q_bircont <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost)) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl}
    (pre_bircont_nL envtyl bpre)
    (post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost))
Proof
  METIS_TAC [prop_holds_TO_bir_step_n_in_L_jgmt_thm, bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_thm]
QED

(* overall symbolic execution to BIR abstract_jgmt_rel *)
Theorem prop_holds_TO_abstract_jgmt_rel_two_thm:
!p start_albl exit_albl_1 exit_albl_2 L envtyl vars bpre bpost_1 bpost_2.
  (<|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> NOTIN L) ==>
  (<|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> NOTIN L) ==>
  (prop_holds (bir_symb_rec_sbir p)
       <|bpc_label := BL_Address start_albl; bpc_index := 0|>
       L
       (P_bircont envtyl bpre)
       (\st st'.
         Q_bircont <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
         Q_bircont <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st')) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl_1; BL_Address exit_albl_2}
    (pre_bircont_nL envtyl bpre)
    (\st st'. 
      post_bircont_nL <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st'))
Proof
  METIS_TAC [prop_holds_TO_bir_step_n_in_L_jgmt_two_thm, bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_SPEC_two_thm]
QED


(* TODO: MOVE THIS AWAY *)
Theorem bir_state_EQ_FOR_VARS_env_vars_are_initialised_thm[local]:
  !st1 st2 vs.
    bir_state_EQ_FOR_VARS vs st1 st2 ==>
    bir_env_vars_are_initialised st1.bst_environ vs ==>
    bir_env_vars_are_initialised st2.bst_environ vs
Proof
  FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def, bir_state_EQ_FOR_VARS_ALT_DEF, bir_envTheory.bir_env_EQ_FOR_VARS_def] >>
  REPEAT STRIP_TAC >>
  REPEAT (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `v`)) >>
  REV_FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>
  METIS_TAC []
QED

(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)
Theorem bir_vars_of_exp_SUBSET_THM_EQ_FOR_VARS:
  !vs st1 st2 e.
    (bir_vars_of_exp e SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_eval_exp e st1.bst_environ = bir_eval_exp e st2.bst_environ)
Proof
  METIS_TAC [bir_envTheory.bir_env_EQ_FOR_VARS_SUBSET, bir_vars_of_exp_THM_EQ_FOR_VARS, bir_state_EQ_FOR_VARS_ALT_DEF]
QED

Theorem pre_bircont_nL_vars_EQ_precond_IMP_thm:
  !vs p bpre envtyl st1 st2.
    (vs = bir_vars_of_program p) ==>
    (bir_vars_of_exp bpre SUBSET vs) ==>
    (ALL_DISTINCT (MAP FST envtyl)) ==>
    (set (MAP PairToBVar envtyl) = vs) ==>
    (st2 = bir_state_restrict_vars vs st1) ==>
    (bir_exec_to_labels_triple_precond st1 bpre p) ==>
    (pre_bircont_nL envtyl bpre st2)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  STRIP_TAC >>

  `bir_envty_list_b envtyl st2.bst_environ` by (
    (* for the reduced state st2, we can prove this *)
    METIS_TAC [bir_state_restrict_vars_envty_list_b_thm, bir_exec_to_labels_triple_precond_def]
  ) >>
  (* we get this from the restriction, the rest must be due to the equality for the variables *)
  `bir_state_EQ_FOR_VARS vs st1 st2` by (
    METIS_TAC [bir_vars_EQ_state_restrict_vars_THM]
  ) >>

  FULL_SIMP_TAC std_ss [pre_bircont_nL_def, bir_exec_to_labels_triple_precond_def] >>
  METIS_TAC [bir_vars_of_exp_SUBSET_THM_EQ_FOR_VARS, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
QED

Theorem post_bircont_nL_vars_EQ_postcond_IMP_thm:
  !vs p bpost exit_albl st1' st2' st2.
    (vs = bir_vars_of_program p) ==>
    (bir_vars_of_exp bpost SUBSET vs) ==>
    (bir_is_bool_exp bpost) ==>
    (bir_state_EQ_FOR_VARS vs st1' st2') ==>
    (post_bircont_nL
       <|bpc_label := BL_Address exit_albl; bpc_index := 0|>
       vs bpost st2 st2') ==>
    (bir_exec_to_labels_triple_postcond st1' (\l. if l = BL_Address exit_albl then bpost else bir_exp_false) p)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [post_bircont_nL_def, bir_exec_to_labels_triple_postcond_def] >>

  `bir_env_vars_are_initialised st1'.bst_environ vs` by (
    METIS_TAC [bir_state_EQ_FOR_VARS_env_vars_are_initialised_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  `st1'.bst_pc.bpc_label = BL_Address exit_albl /\ st1'.bst_pc.bpc_index = 0` by (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
  ) >>
  `bir_is_bool_exp_env st1'.bst_environ bpost` by (
    ASM_REWRITE_TAC [bir_is_bool_exp_env_def] >>
    METIS_TAC [bir_env_vars_are_initialised_SUBSET]
  ) >>
  ASM_SIMP_TAC std_ss [] >>

  METIS_TAC [bir_vars_of_exp_SUBSET_THM_EQ_FOR_VARS, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem abstract_jgmt_rel_bir_exec_to_labels_triple_thm:
!p start_albl exit_albl L envtyl vars bpre bpost.
  (vars = bir_vars_of_program p) ==>
  (bir_vars_of_exp bpre SUBSET vars) ==>
  (bir_vars_of_exp bpost SUBSET vars) ==>
  (bir_is_bool_exp bpost) ==>
  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (set (MAP PairToBVar envtyl) = vars) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl}
    (pre_bircont_nL envtyl bpre)
    (post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost)) ==>
  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl}
    (\st. bir_exec_to_labels_triple_precond st bpre p)
    (\st st'. bir_exec_to_labels_triple_postcond st' (\l. if l = BL_Address exit_albl then bpost else bir_exp_false) p))
Proof
  REWRITE_TAC [abstract_jgmt_rel_def] >>
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vs = bir_vars_of_program p` >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* reduce ms here to a state that only has the program variables and is equal in all program variables, ms_r, then use this new state instead in the next line *)
  Q.ABBREV_TAC `ms_r = bir_state_restrict_vars vs ms` >>
  `bir_state_EQ_FOR_VARS vs ms ms_r` by (
    METIS_TAC [bir_vars_EQ_state_restrict_vars_THM]
  ) >>
  (* here we prove that all the precondition stuff also holds in ms_r *)
  `pre_bircont_nL envtyl bpre ms_r /\ (bir_ts p).ctrl ms_r = BL_Address start_albl` by (
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_ts_def] >>
    FULL_SIMP_TAC (std_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF] >>
    METIS_TAC [pre_bircont_nL_vars_EQ_precond_IMP_thm]
  ) >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPECL [`ms_r`]) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  rename1 `(bir_ts p).weak {BL_Address exit_albl} ms_r ms_r'` >>

  (* because ms_r equals ms in the program variables, we know that the weak transition from ms and ms_r leads to a state that is equal in the program variables *)
  `?ms'. (bir_ts p).weak {BL_Address exit_albl} ms ms' /\ bir_state_EQ_FOR_VARS vs ms' ms_r'` by (
    METIS_TAC [bir_prop_transferTheory.bir_vars_bir_ts_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  Q.EXISTS_TAC `ms'` >>
  REV_FULL_SIMP_TAC (std_ss) [] >>

  (* and because these are equal the postcondition stuff is established as well *)
  METIS_TAC [post_bircont_nL_vars_EQ_postcond_IMP_thm, bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem post_bircont_nL_vars_EQ_postcond_IMP_two_albl_1_thm[local]:
  !vs p bpost_1 bpost_2 exit_albl_1 exit_albl_2 st1' st2' st2.
    (vs = bir_vars_of_program p) ==>
    (bir_vars_of_exp bpost_1 SUBSET vs) ==>
    (bir_is_bool_exp bpost_1) ==>
    (bir_state_EQ_FOR_VARS vs st1' st2') ==>
    (post_bircont_nL
       <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|>
       vs bpost_1 st2 st2') ==>
    (bir_exec_to_labels_triple_postcond st1'
      (\l. if l = BL_Address exit_albl_1 then bpost_1
           else if l = BL_Address exit_albl_2 then bpost_2
           else bir_exp_false) p)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [post_bircont_nL_def, bir_exec_to_labels_triple_postcond_def] >>

  `bir_env_vars_are_initialised st1'.bst_environ vs` by (
    METIS_TAC [bir_state_EQ_FOR_VARS_env_vars_are_initialised_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  `st1'.bst_pc.bpc_label = BL_Address exit_albl_1 /\ st1'.bst_pc.bpc_index = 0` by (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
  ) >>
  sg `bir_is_bool_exp_env st1'.bst_environ bpost_1` >-
   (ASM_REWRITE_TAC [bir_is_bool_exp_env_def] >>
    METIS_TAC [bir_env_vars_are_initialised_SUBSET]) >>
  ASM_SIMP_TAC std_ss [] >>

  METIS_TAC [bir_vars_of_exp_SUBSET_THM_EQ_FOR_VARS, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem post_bircont_nL_vars_EQ_postcond_IMP_two_albl_2_thm[local]:
  !vs p bpost_1 bpost_2 exit_albl_1 exit_albl_2 st1' st2' st2.
    exit_albl_1 <> exit_albl_2 ==>
    (vs = bir_vars_of_program p) ==>
    (bir_vars_of_exp bpost_2 SUBSET vs) ==>
    (bir_is_bool_exp bpost_2) ==>
    (bir_state_EQ_FOR_VARS vs st1' st2') ==>
    (post_bircont_nL
       <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|>
       vs bpost_2 st2 st2') ==>
    (bir_exec_to_labels_triple_postcond st1'
      (\l. if l = BL_Address exit_albl_1 then bpost_1
           else if l = BL_Address exit_albl_2 then bpost_2
           else bir_exp_false) p)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [post_bircont_nL_def, bir_exec_to_labels_triple_postcond_def] >>
  `bir_env_vars_are_initialised st1'.bst_environ vs` by (
    METIS_TAC [bir_state_EQ_FOR_VARS_env_vars_are_initialised_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  `st1'.bst_pc.bpc_label = BL_Address exit_albl_2 /\ st1'.bst_pc.bpc_index = 0` by (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
  ) >>
  sg `bir_is_bool_exp_env st1'.bst_environ bpost_2` >-
   (ASM_REWRITE_TAC [bir_is_bool_exp_env_def] >>
    METIS_TAC [bir_env_vars_are_initialised_SUBSET]) >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `exit_albl_2 = exit_albl_1` >> rw [] >>
  METIS_TAC [bir_vars_of_exp_SUBSET_THM_EQ_FOR_VARS, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem abstract_jgmt_rel_bir_exec_to_two_labels_triple_thm:
!p start_albl exit_albl_1 exit_albl_2 L envtyl vars bpre bpost_1 bpost_2.
  exit_albl_1 <> exit_albl_2 ==>

  (vars = bir_vars_of_program p) ==>
  (bir_vars_of_exp bpre SUBSET vars) ==>

  (bir_vars_of_exp bpost_1 SUBSET vars) ==>
  (bir_vars_of_exp bpost_2 SUBSET vars) ==>

  (bir_is_bool_exp bpost_1) ==>
  (bir_is_bool_exp bpost_2) ==>

  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (set (MAP PairToBVar envtyl) = vars) ==>

  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl_1; BL_Address exit_albl_2}
    (pre_bircont_nL envtyl bpre)
    (\st st'. post_bircont_nL <|bpc_label := BL_Address exit_albl_1; bpc_index := 0|> vars bpost_1 st st' \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl_2; bpc_index := 0|> vars bpost_2 st st')) ==>

  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    {BL_Address exit_albl_1; BL_Address exit_albl_2}
    (\st. bir_exec_to_labels_triple_precond st bpre p)
    (\st st'. bir_exec_to_labels_triple_postcond st'
      (\l. if l = BL_Address exit_albl_1 then bpost_1
           else if l = BL_Address exit_albl_2 then bpost_2
           else bir_exp_false) p))
Proof
  REWRITE_TAC [abstract_jgmt_rel_def] >>
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vs = bir_vars_of_program p` >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* reduce ms here to a state that only has the program variables and is equal in all program variables, ms_r, then use this new state instead in the next line *)
  Q.ABBREV_TAC `ms_r = bir_state_restrict_vars vs ms` >>
  `bir_state_EQ_FOR_VARS vs ms ms_r` by (
    METIS_TAC [bir_vars_EQ_state_restrict_vars_THM]
  ) >>

  (* here we prove that all the precondition stuff also holds in ms_r *)
  `pre_bircont_nL envtyl bpre ms_r /\ (bir_ts p).ctrl ms_r = BL_Address start_albl` by (
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_ts_def] >>
    FULL_SIMP_TAC (std_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF] >>
    METIS_TAC [pre_bircont_nL_vars_EQ_precond_IMP_thm]
  ) >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPECL [`ms_r`]) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  rename1 `(bir_ts p).weak {BL_Address exit_albl_1; BL_Address exit_albl_2} ms_r ms_r'` >>

  (* because ms_r equals ms in the program variables, we know that the weak transition from ms and ms_r leads to a state that is equal in the program variables *)
  `?ms'. (bir_ts p).weak {BL_Address exit_albl_1; BL_Address exit_albl_2} ms ms' /\ bir_state_EQ_FOR_VARS vs ms' ms_r'` by (
    METIS_TAC [bir_prop_transferTheory.bir_vars_bir_ts_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  Q.EXISTS_TAC `ms'` >>
  REV_FULL_SIMP_TAC (std_ss) [] >-

  (* and because these are equal the postcondition stuff is established as well *)
  METIS_TAC [post_bircont_nL_vars_EQ_postcond_IMP_two_albl_1_thm, bir_state_EQ_FOR_VARS_SYM_thm] >-

  METIS_TAC [post_bircont_nL_vars_EQ_postcond_IMP_two_albl_2_thm, GSYM bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem abstract_jgmt_rel_bir_exec_to_two_labels_fmap_thm[local]:
!p start_albl L envtyl vars bpre fm.

  (vars = bir_vars_of_program p) ==>
  (bir_vars_of_exp bpre SUBSET vars) ==>

  ITFMAP (\end_albl bpost vs. vs UNION bir_vars_of_exp bpost) fm {} SUBSET vars ==>

  ITFMAP (\end_albl bpost Bs. Bs /\ bir_is_bool_exp bpost) fm T ==>

  (ALL_DISTINCT (MAP FST envtyl)) ==>
  (set (MAP PairToBVar envtyl) = vars) ==>

  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    (IMAGE (\exit_albl. BL_Address exit_albl) (FDOM fm))
    (pre_bircont_nL envtyl bpre)
    (\st st'. ITFMAP (\exit_albl bpost pLs. pLs \/
      post_bircont_nL <|bpc_label := BL_Address exit_albl; bpc_index := 0|> vars bpost st st') fm F)) ==>

  (abstract_jgmt_rel
    (bir_ts p)
    (BL_Address start_albl)
    (IMAGE (\exit_albl. BL_Address exit_albl) (FDOM fm))
    (\st. bir_exec_to_labels_triple_precond st bpre p)
    (\st st'. bir_exec_to_labels_triple_postcond st'
      (\l. case l of
           | BL_Label s => bir_exp_false
           | BL_Address addr =>
             (case FLOOKUP fm addr of
              | SOME bpost => bpost
              | NONE => bir_exp_false)) p))
Proof
 cheat
QED

val _ = export_theory ();
