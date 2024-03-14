
open HolKernel Parse boolLib bossLib;

open bir_symbTheory;

open birs_stepLib;
open birs_composeLib;

open birs_auxTheory;

  open birs_stepLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open birs_composeLib;
open birs_auxTheory;

open bir_program_transfTheory;
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);




val _ = new_theory "motorfunc_transf";



val bprog_def = motorfuncTheory.bprog_def;
val bprog = (fst o dest_eq o concl) bprog_def;
val bprog_tm = (fst o dest_eq o concl) bprog_def;




val m0_mod_vars_def = bir_program_transfTheory.m0_mod_vars_def;

val m0_mod_vars_thm = bir_program_transfTheory.m0_mod_vars_thm;

val birenvtyl_def = bir_program_transfTheory.birenvtyl_def;

val birenvtyl_EVAL_thm = bir_program_transfTheory.birenvtyl_EVAL_thm;







(*
    ``bprecond = BExp_Const (Imm1 1w)``
*)
Definition bprecond_def:
  bprecond = BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
End
val bprecond = (fst o dest_eq o concl) bprecond_def;

(* need to translate the precondition to a symbolic pathcondition, it means taking from the environment the corresponding mappings and substitute (that's symbolic evaluation) (then we know that states with matching environments also satisfy the original precondition because it is constructed by symbolic evaluation) *)
Definition bsysprecond_def:
  bsysprecond = FST (THE (birs_eval_exp ^bprecond (bir_senv_GEN_list birenvtyl)))
End
val bprecond_birs_eval_exp_thm = save_thm(
   "bprecond_birs_eval_exp_thm",
  (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC
   birs_stepLib.birs_eval_exp_CONV)
     ``birs_eval_exp bprecond (bir_senv_GEN_list birenvtyl)``
);
val bsysprecond_thm = save_thm(
   "bsysprecond_thm",
  (REWRITE_CONV [bsysprecond_def, birs_eval_exp_ALT_thm, bprecond_birs_eval_exp_thm] THENC EVAL) ``bsysprecond``
);
val bprecond_birs_eval_exp_thm2 = save_thm(
   "bprecond_birs_eval_exp_thm2",
  REWRITE_CONV [bprecond_birs_eval_exp_thm, GSYM bsysprecond_thm] ``birs_eval_exp bprecond (bir_senv_GEN_list birenvtyl)``
);
val bsysprecond = (fst o dest_eq o concl) bsysprecond_def;


val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb46w))``;


val birs_state_init_pre = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := ^bsysprecond
|>``;
val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) motorfuncTheory.bin_motor_func_analysis_thm;

val birs_state_init_pre_EQ_thm =
REWRITE_RULE [] ((REWRITE_CONV [bsysprecond_thm] THENC
  SIMP_CONV (std_ss++birs_state_ss++holBACore_ss) [] THENC
  EVAL)
  ``^((snd o dest_comb) sys_i) = ^birs_state_init_pre``);

val motor_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm] motorfuncTheory.bin_motor_func_analysis_thm;

val birs_state_thm = REWRITE_CONV [birenvtyl_EVAL_thm] birs_state_init_pre;


Definition motor_analysis_L_def:
  motor_analysis_L = ^(L_s)
End



(* ........................... *)



(* now the transfer *)
(* ........................... *)

(* prepare property transfer theorem *)
val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);
(* ........................... *)


(* basic definitions for the property we want to prove (countw) *)
Definition bprog_P_def:
  bprog_P ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       pc.bpc_index = 0 /\
       bir_envty_list birenvtyl st /\
       bir_eval_exp ^bprecond (BEnv st) = SOME bir_val_true)
End
(* translate the property to BIR state property *)
Theorem bprog_P_thm:
  !bs.
  bprog_P (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bs.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl bs.bst_environ /\
       bir_eval_exp ^bprecond bs.bst_environ = SOME bir_val_true)
Proof
REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_P_def, bir_envty_list_b_thm, bir_BEnv_lookup_EQ_thm]
QED

(* this is the relevant property about the cycle counter *)
Definition bprog_Q_def:
  bprog_Q
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (
       (pc2 = ^birs_state_end_lbl)
       /\
       (status2 = BST_Running /\
        ?v1 v2. (st1 "countw" = SOME (BVal_Imm (Imm64 v1))) /\
                (st2 "countw" = SOME (BVal_Imm (Imm64 v2))) /\
                (v1 <=+ 0xFFFFFFFFFFFFFF00w) /\
                (v1 + 44w <=+ v2) /\
                (v2 <=+ v1 + 47w))
     )
End
Theorem bprog_Q_thm:
  !bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = ^birs_state_end_lbl)
      /\
      (bs2.bst_status = BST_Running /\
       ?v1 v2. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v1)) /\
               bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 v2)) /\
               (v1 <=+ 0xFFFFFFFFFFFFFF00w) /\
               (v1 + 44w <=+ v2) /\
               (v2 <=+ v1 + 47w))
    )
Proof
FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
QED
(* ........................... *)

(* P is generic enough *)

Theorem bprog_P_entails_thm:
  P_entails_an_interpret (bir_symb_rec_sbir ^bprog) bprog_P (birs_symb_to_symbst ^birs_state_init_pre)
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

  `(ALL_DISTINCT (MAP FST birenvtyl))` by EVAL_TAC >>

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


Theorem bir_env_read_countw_lookup_thm:
  !env v.
  (bir_env_lookup "countw" env = SOME (BVal_Imm (Imm64 v))) ==>
  (bir_env_read (BVar "countw" (BType_Imm Bit64)) env = SOME (BVal_Imm (Imm64 v)))
Proof
Cases_on `env` >>

  FULL_SIMP_TAC std_ss [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED


(* Q is implied by sys and Pi *)
Theorem bprog_Pi_overapprox_Q_thm:
  Pi_overapprox_Q (bir_symb_rec_sbir ^bprog) bprog_P (birs_symb_to_symbst ^birs_state_init_pre) ^Pi_f(*(IMAGE birs_symb_to_symbst {a;b;c;d})*) bprog_Q
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
    (* countw property *)

    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H` by (
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
    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
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

    `symb_interpr_get H' (BVar "sy_countw" (BType_Imm Bit64)) = symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def]
    ) >>

    `bir_eval_exp bprecond bs.bst_environ = SOME bir_val_true` by (
      Q.UNABBREV_TAC `sys1` >>
      FULL_SIMP_TAC (std_ss) [bprog_P_thm]
    ) >>

    (* *)

    `?v1. symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64)) = SOME (BVal_Imm (Imm64 v1))` by (
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

      `bir_val_is_Imm_s Bit64 x` by (
        METIS_TAC [bir_valuesTheory.bir_val_checker_TO_type_of]
      ) >>
      FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_is_Imm_s_def, bir_immTheory.n2bs_def] >>

      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

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
  )
QED
(* ........................... *)

(* apply the theorem for property transfer *)
val bprog_prop_holds_thm =
  MATCH_MP
    (MATCH_MP
      (MATCH_MP
         birs_prop_transfer_thm
         bprog_P_entails_thm)
      bprog_Pi_overapprox_Q_thm)
    motor_analysis_thm;

(* lift to concrete state property *)
val bprog_concst_prop_thm =
  SIMP_RULE (std_ss++birs_state_ss)
    [birs_symb_symbst_pc_thm]
    (REWRITE_RULE
      [symb_prop_transferTheory.prop_holds_def]
      bprog_prop_holds_thm);
(* ........................... *)


(* lift to concrete bir property *)
val st_init_lbl = (snd o dest_eq o hd o fst o strip_imp o snd o strip_forall o concl) bprog_concst_prop_thm;
(* TODO: we probably need a better way to "summarize/overapproximate" the labels of the program, check that this is possible and none of the rules break this *)
val bprog_lbls  = List.nth ((snd o strip_comb o fst o dest_conj o snd o strip_exists o snd o strip_imp o snd o strip_forall o concl) bprog_concst_prop_thm, 3);
Theorem bprog_to_concst_prop_thm:
  !st.
  (symb_concst_pc (birs_symb_to_concst st) = (^st_init_lbl)) ==>
  (bprog_P (birs_symb_to_concst st)) ==>
  (?n st'.
     (step_n_in_L
       (symb_concst_pc o birs_symb_to_concst)
       (SND o bir_exec_step (^bprog))
       st
       n
       (^bprog_lbls)
       st')
     /\
     (bprog_Q (birs_symb_to_concst st) (birs_symb_to_concst st')))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC (HO_MATCH_MP birs_symb_to_concst_PROP_FORALL_thm bprog_concst_prop_thm) >>

  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [conc_step_n_in_L_def, bir_symb_rec_sbir_def] >>

  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [] >>

  `birs_symb_to_concst o SND o bir_exec_step ^bprog o
             birs_symb_from_concst =
   birs_symb_to_concst o (SND o bir_exec_step ^bprog) o
             birs_symb_from_concst` by (
    FULL_SIMP_TAC (std_ss) []
  ) >>
  FULL_SIMP_TAC (pure_ss) [] >>

  FULL_SIMP_TAC (pure_ss) [
    SIMP_RULE std_ss [birs_symb_to_from_concst_thm, birs_symb_to_concst_EXISTS_thm, birs_symb_to_concst_EQ_thm] (
      SPECL [``birs_symb_to_concst``, ``birs_symb_from_concst``] (
        INST_TYPE [beta |-> Type`:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t`, alpha |-> Type`:bir_state_t`] step_n_in_L_ABS_thm)
  )] >>

  METIS_TAC []
QED

(* finish translation to pure BIR property *)
val bprog_bir_prop_thm = save_thm(
   "bprog_bir_prop_thm",
  REWRITE_RULE
    [bprog_P_thm, bprecond_def, bprog_Q_thm, birs_symb_concst_pc_thm, combinTheory.o_DEF, GSYM bir_programTheory.bir_exec_step_state_def, GSYM motor_analysis_L_def]
    (REWRITE_RULE
      []
      bprog_to_concst_prop_thm)
);
(* ........................... *)

val bir_frag_l_tm = ``<|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>``;
val bir_frag_l_ml_tm = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl o EVAL) ``(^bir_frag_l_tm).bpc_label``;

val bir_frag_l_exit_ml_tm = ``2886w:word32``;
val bir_frag_l_exit_tm = ``<|bpc_label := BL_Address (Imm32 ^bir_frag_l_exit_ml_tm); bpc_index := 0|>``;

Definition bprecond_def:
  bprecond =
         BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
               (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
               (BExp_Aligned Bit32 2
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
End

Definition pre_bir_def:
  pre_bir bs =
       (bir_eval_exp bprecond bs.bst_environ = SOME bir_val_true)
End

Definition post_bir_def:
  post_bir bs1 bs2 =
      (?v1 v2. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v1)) /\
               bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 v2)) /\
               (v1 <=+ 0xFFFFFFFFFFFFFF00w) /\
               (v1 + 44w <=+ v2) /\
               (v2 <=+ v1 + 47w))
(*
           v1 <+ v2 /\
           v1 + 44w <=+ v2 /\
           v2 <=+ v1 + 47w
*)
End

Definition pre_bir_nL_def:
  pre_bir_nL st =
      (
       st.bst_status = BST_Running /\
       st.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl st.bst_environ /\

       pre_bir st
      )
End
Definition post_bir_nL_def:
  post_bir_nL (st:bir_state_t) st' =
      (
         (st'.bst_pc = ^bir_frag_l_exit_tm) /\
         st'.bst_status = BST_Running /\

         post_bir st st'
      )
End

Theorem bir_step_n_in_L_jgmt_thm[local]:
  bir_step_n_in_L_jgmt
  ^bprog_tm
  ^bir_frag_l_tm
  motor_analysis_L
  pre_bir_nL
  post_bir_nL
Proof
REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  REWRITE_TAC [pre_bir_nL_def, pre_bir_def, bprecond_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPEC `st` bprog_bir_prop_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [
     prove(``(\x. bir_exec_step_state ^(bprog_tm) x) = bir_exec_step_state ^(bprog_tm)``, MATCH_MP_TAC boolTheory.EQ_EXT >> SIMP_TAC std_ss [])
    ] >>
  Q.EXISTS_TAC `n` >>
  Q.EXISTS_TAC `st'` >>
  ASM_SIMP_TAC std_ss [] >>

  REWRITE_TAC [post_bir_nL_def, post_bir_def] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED


Theorem motor_analysis_L_INTER_thm[local]:
  motor_analysis_L INTER
        {<|bpc_label := BL_Address (Imm32 2886w); bpc_index := 0|>} =
        EMPTY
Proof
`!A B. A INTER {B} = (EMPTY:bir_programcounter_t -> bool) <=> B NOTIN A` by (
    REPEAT STRIP_TAC >>
    EQ_TAC >> (
      FULL_SIMP_TAC std_ss [bir_auxiliaryTheory.SING_DISJOINT_SING_NOT_IN_thm]
    ) >>
    REPEAT STRIP_TAC >>

    REWRITE_TAC [Once (GSYM INTER_COMM)] >>
    FULL_SIMP_TAC std_ss [INTER_EMPTY, INSERT_INTER]
  ) >>
  POP_ASSUM (fn thm => ASM_REWRITE_TAC [thm]) >>

  EVAL_TAC
QED

Theorem bir_abstract_jgmt_rel_motor_thm[local]:
  abstract_jgmt_rel
  (bir_ts ^bprog_tm)
  (BL_Address (Imm32 ^bir_frag_l_ml_tm))
  {BL_Address (Imm32 ^bir_frag_l_exit_ml_tm)}
  pre_bir_nL
  post_bir_nL
Proof
ASSUME_TAC
    (Q.SPEC `{BL_Address (Imm32 ^bir_frag_l_exit_ml_tm)}`
      (MATCH_MP
        (REWRITE_RULE
           [bir_programTheory.bir_block_pc_def]
           bir_program_transfTheory.bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm)
        bir_step_n_in_L_jgmt_thm)) >>

  FULL_SIMP_TAC std_ss [pre_bir_nL_def] >>

  FULL_SIMP_TAC std_ss [IMAGE_SING, IN_SING, bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [motor_analysis_L_INTER_thm] >>

  FULL_SIMP_TAC std_ss [post_bir_nL_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [abstract_jgmt_rel_def]
QED

val bmemms_t = List.nth((snd o strip_comb o concl) bin_motor_funcTheory.bin_motor_func_thm, 2);
Definition bmemms_def:
  bmemms = ^(bmemms_t)
End
val bin_motor_func_thm = REWRITE_RULE [GSYM bmemms_def, GSYM bprog_def] bin_motor_funcTheory.bin_motor_func_thm;


(* TODO: COPIED STUFF *)
(* =================================================================================== *)
Theorem bmr_rel_m0_mod_bmr_IMP_index_thm[local]:
  !ms bs.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bs.bst_status = BST_Running) ==>
  (bs.bst_pc.bpc_index = 0)
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "countw" bs.bst_environ = SOME (BVal_Imm (Imm64 ms.countw)))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_SP_process_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "SP_process" bs.bst_environ = SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_process))))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED
(* =================================================================================== *)

(*
  transfer of relational postcondition to machine model
*)
Definition pre_m0_mod_def:
  pre_m0_mod ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms) bmemms) /\
        ((m0_mod_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.base.REG RName_SP_process /\
         ms.base.REG RName_SP_process && 0x3w = 0w /\
         ms.countw <=+ 0xFFFFFFFFFFFFFF00w)
      )
End
Definition post_m0_mod_def:
  post_m0_mod ms ms' =
      (
        (ms.countw <=+ 0xFFFFFFFFFFFFFF00w) /\
        (ms.countw + 44w <=+ ms'.countw) /\
        (ms'.countw <=+ ms.countw + 47w)
      )
End

Theorem backlift_bir_m0_mod_pre_abstr_ex_thm[local]:
  backlift_bir_m0_mod_pre_abstr pre_m0_mod pre_bir_nL
Proof
FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_pre_abstr_def, pre_m0_mod_def, pre_bir_nL_def, pre_bir_def] >>
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>

  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_index_thm >>
  FULL_SIMP_TAC std_ss [] >>

  REWRITE_TAC [bprecond_def] >>
  EVAL_TAC >>

  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm >>
  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_SP_process_lookup_thm >>
  ASM_REWRITE_TAC [] >>
  EVAL_TAC >>
  ASM_REWRITE_TAC [] >>
  EVAL_TAC
QED

Theorem backlift_bir_m0_mod_post_concr_ex_thm[local]:
  backlift_bir_m0_mod_post_concr post_bir_nL post_m0_mod
Proof
FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_post_concr_def, post_bir_nL_def, post_m0_mod_def, post_bir_def] >>
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  `v1 = ms.countw` by (
    IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  `v2 = ms'.countw` by (
    IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  FULL_SIMP_TAC (std_ss) []
QED

Theorem m0_mod_thm[local]:
  abstract_jgmt_rel
  m0_mod_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  pre_m0_mod
  post_m0_mod
Proof
ASSUME_TAC
    (Q.SPECL
      [`pre_m0_mod`, `pre_bir_nL`, `post_bir_nL`, `post_m0_mod`, `(^bir_frag_l_ml_tm)`, `{^bir_frag_l_exit_ml_tm}`]
      (MATCH_MP
        bir_program_transfTheory.backlift_bir_m0_mod_contract_thm
        (bin_motor_func_thm))) >>

  `!ms. pre_m0_mod ms ==>
           EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms) bmemms` by (
    FULL_SIMP_TAC std_ss [pre_m0_mod_def]
  ) >>

  `!ms. pre_m0_mod ms ==> (m0_mod_bmr (F,T)).bmr_extra ms` by (
    FULL_SIMP_TAC std_ss [pre_m0_mod_def]
  ) >>

  `!bs.    pre_bir_nL bs ==>
           ~bir_state_is_terminated bs` by (
    FULL_SIMP_TAC std_ss [pre_bir_nL_def, bir_programTheory.bir_state_is_terminated_def]
  ) >>

  `MEM (BL_Address (Imm32 ^bir_frag_l_ml_tm)) (bir_labels_of_program (bprog:'observation_type bir_program_t))` by (
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `!bs bs'. post_bir_nL bs bs' ==> ~bir_state_is_terminated bs'` by (
    FULL_SIMP_TAC std_ss [post_bir_nL_def, bir_programTheory.bir_state_is_terminated_def]
  ) >>

  ASSUME_TAC backlift_bir_m0_mod_pre_abstr_ex_thm >>
  ASSUME_TAC backlift_bir_m0_mod_post_concr_ex_thm >>

  FULL_SIMP_TAC std_ss [IMAGE_SING, IN_SING] >>
  FULL_SIMP_TAC std_ss [bir_abstract_jgmt_rel_motor_thm] >>
  METIS_TAC []
QED


(* TODO: MORE COPIED STUFF *)
(* =================================================================================== *)
Theorem m0_mod_R_IMP_bmr_ms_mem_contains_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (bmr_ms_mem_contains (m0_mod_bmr (F,T)) mms =
   bmr_ms_mem_contains (m0_bmr (F,T)) ms)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  MATCH_MP_TAC boolTheory.EQ_EXT >>
  Cases_on `x` >>

  `(mms.base with count := w2n mms.countw).MEM = mms.base.MEM` by (
    SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
  ) >>

  Q.SPEC_TAC (`q`, `b`) >>
  Q.SPEC_TAC (`r`, `l`) >>

  Induct_on `l` >- (
    GEN_TAC >>
    EVAL_TAC
  ) >>

  REWRITE_TAC [bir_lifting_machinesTheory.bmr_ms_mem_contains_def] >>
  REPEAT STRIP_TAC >>
  POP_ASSUM (fn thm => SIMP_TAC std_ss [thm]) >>

  SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_mem_lf_def] >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.m0_mod_lifted_mem_def, bir_lifting_machinesTheory.m0_lifted_mem_def] >>
  CASE_TAC >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.bir_machine_lifted_mem_t_11] >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED
Theorem m0_mod_R_IMP_REG_EQ_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (mms.base.REG = ms.REG)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED
Theorem m0_mod_R_IMP_bmr_extra_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  ((m0_mod_bmr (F,T)).bmr_extra mms = (m0_bmr (F,T)).bmr_extra ms)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.m0_mod_state_is_OK_def, bir_lifting_machinesTheory.m0_state_is_OK_def] >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED
Theorem m0_mod_R_IMP_count_EQ_countw_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (ms.count = w2n mms.countw)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED

(* =================================================================================== *)

(*
transfer to (unmodified) m0 model
*)

Definition pre_m0_def:
  pre_m0 ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_bmr (F,T)) ms) bmemms) /\
        ((m0_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.REG RName_SP_process /\
         ms.REG RName_SP_process && 0x3w = 0w /\
         ms.count <= 0xFFFFFFFFFFFFFF00:num)
      )
End
Definition post_m0_def:
  post_m0 ms ms' =
      (
        (ms.count + 44 <= ms'.count) /\
        (ms'.count <= ms.count + 47)
      )
End



Theorem backlift_m0_mod_m0_pre_abstr_ex_thm[local]:
  backlift_m0_mod_m0_pre_abstr (pre_m0) (pre_m0_mod)
Proof
FULL_SIMP_TAC std_ss [pre_m0_def, pre_m0_mod_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>

  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  `(EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) mms) bmemms) /\
        ((m0_mod_bmr (F,T)).bmr_extra mms)` by (
    METIS_TAC [m0_mod_R_IMP_bmr_ms_mem_contains_thm, m0_mod_R_IMP_bmr_extra_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `0xFFFFFFw <=+ mms.base.REG RName_SP_process /\
   mms.base.REG RName_SP_process && 0x3w = 0w` by (
    METIS_TAC [m0_mod_R_IMP_REG_EQ_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

(*
         ms.count <= 0xFFFFFFFFFFFFFF00:num ==>
         ms.countw <=+ 0xFFFFFFFFFFFFFF00w
*)
  REWRITE_TAC [wordsTheory.WORD_LS] >>

  IMP_RES_TAC m0_mod_R_IMP_count_EQ_countw_thm >>
  POP_ASSUM (fn thm => REWRITE_TAC [GSYM thm]) >>
  EVAL_TAC >>
  ASM_REWRITE_TAC []
QED

Theorem backlift_m0_mod_m0_post_concr_ex_thm[local]:
  backlift_m0_mod_m0_post_concr post_m0_mod post_m0
Proof
FULL_SIMP_TAC std_ss [post_m0_mod_def, post_m0_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  IMP_RES_TAC m0_mod_R_IMP_count_EQ_countw_thm >>
  ASM_REWRITE_TAC [] >>

  POP_ASSUM (K ALL_TAC) >>
  POP_ASSUM (K ALL_TAC) >>
  REPEAT (PAT_X_ASSUM ``m0_mod_R A B`` (K ALL_TAC)) >>
  Q.ABBREV_TAC `x = mms.countw` >>
  Q.ABBREV_TAC `y = mms'.countw` >>
  POP_ASSUM (K ALL_TAC) >>
  POP_ASSUM (K ALL_TAC) >>

  `w2n x + 44 = w2n (x + 44w)` by (
    `w2n (x + 44w) = (w2n x + 44) MOD dimword (:64)` by (
      REWRITE_TAC [GSYM wordsTheory.w2n_n2w] >>
      REWRITE_TAC [GSYM wordsTheory.word_add_n2w] >>
      REWRITE_TAC [wordsTheory.n2w_w2n]
    ) >>
    ASM_REWRITE_TAC [] >>

    `(w2n x + 44) < dimword (:64)` by (
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [wordsTheory.WORD_LS] >>
      POP_ASSUM MP_TAC >>
      EVAL_TAC >>
      STRIP_TAC >>

      REWRITE_TAC [GSYM (EVAL ``^((snd o dest_eq o concl o EVAL) ``(18446744073709551616 - 44:num)``) + 44``)] >>
      REWRITE_TAC [arithmeticTheory.LT_ADD_RCANCEL] >>

      MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS >>
      HINT_EXISTS_TAC >>

      ASM_REWRITE_TAC [] >>
      EVAL_TAC
    ) >>

    METIS_TAC [arithmeticTheory.LESS_MOD]
  ) >>
  `w2n x + 47 = w2n (x + 47w)` by (
    `w2n (x + 47w) = (w2n x + 47) MOD dimword (:64)` by (
      REWRITE_TAC [GSYM wordsTheory.w2n_n2w] >>
      REWRITE_TAC [GSYM wordsTheory.word_add_n2w] >>
      REWRITE_TAC [wordsTheory.n2w_w2n]
    ) >>
    ASM_REWRITE_TAC [] >>

    `(w2n x + 47) < dimword (:64)` by (
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [wordsTheory.WORD_LS] >>
      POP_ASSUM MP_TAC >>
      EVAL_TAC >>
      STRIP_TAC >>

      REWRITE_TAC [GSYM (EVAL ``^((snd o dest_eq o concl o EVAL) ``(18446744073709551616 - 47:num)``) + 47``)] >>
      REWRITE_TAC [arithmeticTheory.LT_ADD_RCANCEL] >>

      MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS >>
      HINT_EXISTS_TAC >>

      ASM_REWRITE_TAC [] >>
      EVAL_TAC
    ) >>

    METIS_TAC [arithmeticTheory.LESS_MOD]
  ) >>
  ASM_SIMP_TAC std_ss [] >>
  POP_ASSUM (K ALL_TAC) >>
  POP_ASSUM (K ALL_TAC) >>

  FULL_SIMP_TAC std_ss [wordsTheory.WORD_LS]
QED

Theorem m0_thm:
  abstract_jgmt_rel
  m0_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  (pre_m0)
  (post_m0)
Proof
ASSUME_TAC
    (Q.SPECL
      [`pre_m0`, `pre_m0_mod`, `post_m0_mod`, `post_m0`, `(^bir_frag_l_ml_tm)`, `{^bir_frag_l_exit_ml_tm}`]
      bir_program_transfTheory.backlift_m0_mod_m0_contract_thm) >>

  `!ms. pre_m0 ms ==> (\ms. ms.count < 2 ** 64) ms` by (
    FULL_SIMP_TAC std_ss [pre_m0_def] >>
    REPEAT STRIP_TAC >>

(*
    IMP_RES_TAC arithmeticTheory.LESS_EQ_IMP_LESS_SUC >>
    POP_ASSUM (ASSUME_TAC o CONV_RULE EVAL) >>
*)
    IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS >>
    POP_ASSUM MATCH_MP_TAC >>
    EVAL_TAC
  ) >>

  ASSUME_TAC backlift_m0_mod_m0_pre_abstr_ex_thm >>
  ASSUME_TAC backlift_m0_mod_m0_post_concr_ex_thm >>

  FULL_SIMP_TAC std_ss [m0_mod_thm]
QED

val m0_EVAL_thm = save_thm(
   "m0_EVAL_thm",
  REWRITE_RULE
   [pre_m0_def, post_m0_def,
    prove(``pre_m0 = (\ms. pre_m0 ms)``, MATCH_MP_TAC boolTheory.EQ_EXT >> FULL_SIMP_TAC std_ss []),
    prove(``post_m0 = (\ms ms'. post_m0 ms ms')``, MATCH_MP_TAC boolTheory.EQ_EXT >> FULL_SIMP_TAC std_ss [] >> GEN_TAC >> MATCH_MP_TAC boolTheory.EQ_EXT >> FULL_SIMP_TAC std_ss [])]
   m0_thm
);

val _ = export_theory();

val result = m0_EVAL_thm;

val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);
