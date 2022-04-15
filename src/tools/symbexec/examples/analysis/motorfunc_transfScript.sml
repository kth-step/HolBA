
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

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "motorfunc_transf";

val _ = export_theory();



val bprog_def = motorfuncTheory.bprog_def;
val bprog = (fst o dest_eq o concl) bprog_def;




val m0_mod_vars_def = motorfuncTheory.m0_mod_vars_def;

val m0_mod_vars_thm = motorfuncTheory.m0_mod_vars_thm;

val birenvtyl_def = motorfuncTheory.birenvtyl_def;

val birenvtyl_EVAL_thm = motorfuncTheory.birenvtyl_EVAL_thm;







(*
    ``bprecond = BExp_Const (Imm1 1w)``
*)
val bprecond_def = Define `
    bprecond = BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
`;
val bprecond = (fst o dest_eq o concl) bprecond_def;

(* need to translate the precondition to a symbolic pathcondition, it means taking from the environment the corresponding mappings and substitute (that's symbolic evaluation) (then we know that states with matching environments also satisfy the original precondition because it is constructed by symbolic evaluation) *)
val bsysprecond_def = Define `
    bsysprecond = FST (THE (birs_eval_exp ^bprecond (bir_senv_GEN_list birenvtyl)))
`;
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


val motor_analysis_L_def = Define `
    motor_analysis_L = ^(L_s)
`;



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
val bprog_P_def = Define `
    bprog_P ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       bir_envty_list birenvtyl st /\
       bir_eval_exp ^bprecond (BEnv st) = SOME bir_val_true)
`;
(* translate the property to BIR state property *)
val bprog_P_thm = store_thm(
   "bprog_P_thm", ``
!bs.
  bprog_P (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bir_envty_list_b birenvtyl bs.bst_environ /\
       bir_eval_exp ^bprecond bs.bst_environ = SOME bir_val_true)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_P_def, bir_envty_list_b_thm, bir_BEnv_lookup_EQ_thm]
);

(* this is the relevant property about the cycle counter *)
val bprog_Q_def = Define `
    bprog_Q
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (
       (pc2 = ^birs_state_end_lbl)
       /\
       (?v1 v2. (st1 "countw" = SOME (BVal_Imm (Imm64 v1))) /\
                (st2 "countw" = SOME (BVal_Imm (Imm64 v2))) /\
                (v1 <+ v2) /\
                (v1 + 44w <=+ v2) /\
                (v2 <=+ v1 + 47w))
     )
`;
val bprog_Q_thm = store_thm(
   "bprog_Q_thm", ``
!bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = ^birs_state_end_lbl)
      /\
      (?v1 v2. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v1)) /\
               bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 v2)) /\
               (v1 <+ v2) /\
               (v1 + 44w <=+ v2) /\
               (v2 <=+ v1 + 47w))
    )
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
);
(* ........................... *)

(* P is generic enough *)

val bprog_P_entails_thm = store_thm(
   "bprog_P_entails_thm", ``
P_entails_an_interpret (bir_symb_rec_sbir ^bprog) bprog_P (birs_symb_to_symbst ^birs_state_init_pre)
``,
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
);

(* ........................... *)

(* Q is implied by sys and Pi *)
val bprog_Pi_overapprox_Q_thm = store_thm(
   "bprog_Pi_overapprox_Q_thm", ``
Pi_overapprox_Q (bir_symb_rec_sbir ^bprog) bprog_P (birs_symb_to_symbst ^birs_state_init_pre) ^Pi_f bprog_Q
``,
  cheat >>

  SIMP_TAC std_ss [(REWRITE_RULE [EVAL ``birenvtyl``] o EVAL) ``bir_senv_GEN_list birenvtyl``, bsysprecond_thm] >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) [Pi_overapprox_Q_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss) [] >>
  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss) [] >>

  FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, pred_setTheory.IN_INSERT] >> REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss) [pred_setTheory.NOT_IN_EMPTY]
  ) >> (
    PAT_X_ASSUM ``A = birs_symb_to_symbst B`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>

    FULL_SIMP_TAC (std_ss) [bprog_Q_thm] >>
    FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

    REPEAT (PAT_X_ASSUM ``symb_interpr_for_symbs (birs_symb_symbols A) B``
      (fn thm =>
         let
           val tm = (hd o snd o strip_comb o concl) thm;
           val birs_exps_of_senv_CONV = (
    REPEATC (CHANGED_CONV (
      (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (EVAL)))) THENC
      SIMP_CONV (std_ss) []
    ))
  );

           val birs_symb_symbols_CONV = (
    SIMP_CONV std_ss [birs_symb_symbols_thm] THENC
    SIMP_CONV (std_ss++birs_state_ss) [] THENC
    SIMP_CONV (std_ss) [birs_exps_of_senv_thm] THENC
    DEPTH_CONV (PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` birs_exps_of_senv_CONV)
  );
(*
birenvtyl_EVAL_thm
val tm = ``
  birs_symb_symbols
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2826w); bpc_index := 2|>;
    bsst_environ :=
      (K NONE)⦇
        "countw" ↦
          SOME
            (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 1w)));
        "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
        "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
        "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
        "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
        "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
        "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
        "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
        "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
        "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
        "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
        "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
        "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
        "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
        "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
        "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
        "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
        "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
        "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
        "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
        "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
        "SP_process" ↦
          SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
        "ModeHandler" ↦
          SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
        "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
      ⦈; bsst_status := BST_Running; bsst_pcond := (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                   (BExp_Den (BVar "sy_R1" (BType_Imm Bit32))))|>``;

birs_symb_symbols_CONV tm

val tm2 = ``birs_exps_of_senv_COMP {} 
             (K NONE)⦇
               "countw" ↦
                 SOME
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 1w)));
               "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
               "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
               "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
               "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
               "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
               "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
               "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
               "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
               "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
               "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
               "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
               "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
               "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
               "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
               "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
               "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
               "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
               "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
               "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
               "SP_main" ↦
                 SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
               "SP_process" ↦
                 SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
               "ModeHandler" ↦
                 SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
               "countw" ↦
                 SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             ⦈``;
val tm2 = ``birs_exps_of_senv_COMP {} 
             (K NONE)⦇
               "countw" ↦
                 SOME
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 1w)));
               "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
             ⦈``;

birs_exps_of_senv_CONV tm2

*)
           val _ = print_term tm; 
           val conv = birs_symb_symbols_CONV THENC EVAL;
           val thm_res = (computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv) tm;
           val _ = print_term (concl thm_res);
         in
           ASSUME_TAC (REWRITE_RULE [Once thm_res] thm)
         end)) >>

    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H` by (
      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>
    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def] >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"countw"`)) >>
    FULL_SIMP_TAC (std_ss) [] >>

    `symb_interpr_get H' (BVar "sy_countw" (BType_Imm Bit64)) = symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def]
    ) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_interpr_welltyped_def] >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `BVar "sy_countw" (BType_Imm Bit64)`)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    Cases_on `symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` >- (
      METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, optionTheory.option_CLAUSES]
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES] >>

    FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.bir_vars_of_exp_def, UNION_EMPTY, bir_exp_subst_def, bir_exp_subst_var_def, FINITE_SING, finite_mapTheory.FLOOKUP_FUN_FMAP, IN_SING, birs_interpret_subst_fmap_get_def] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    `bir_val_is_Imm_s Bit64 x` by (
      METIS_TAC [bir_valuesTheory.bir_val_checker_TO_type_of]
    ) >>
    FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_is_Imm_s_def, bir_immTheory.n2bs_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_to_constexp_def] >>
    REPEAT (PAT_X_ASSUM ``BVal_Imm (Imm64 (n2w B)) = A`` (ASSUME_TAC o GSYM)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_to_constexp_def]


(*
Q.EXISTS_TAC `n2w n + 44w`
    FULL_SIMP_TAC (std_ss++holBACore_ss) []

*)

  )
);
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
val bprog_to_concst_prop_thm = store_thm(
   "bprog_to_concst_prop_thm", ``
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
``,
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
);

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

val bir_step_n_in_L_jgmt_def = Define `
    bir_step_n_in_L_jgmt bprog l L pre post =
 !st.
   (st.bst_pc = l) ==>
   (pre st) ==>
   (?n st'.
     (step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) st n L st') /\
     (post st st'))
`;

val bir_step_n_in_L_jgmt_thm = prove(``
(bir_step_n_in_L_jgmt
  bprog
  <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>
  motor_analysis_L
  (\st.
       st.bst_status = BST_Running /\
       bir_envty_list_b birenvtyl st.bst_environ /\
       bir_eval_exp
         (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
               (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
               (BExp_Aligned Bit32 2
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))) st.bst_environ =
       SOME bir_val_true)
  (\st st'.
         (st'.bst_pc = <|bpc_label := BL_Address (Imm32 2886w); bpc_index := 0|>) /\
         ?v1 v2.
           bir_env_lookup "countw" st.bst_environ =
           SOME (BVal_Imm (Imm64 v1)) /\
           bir_env_lookup "countw" st'.bst_environ =
           SOME (BVal_Imm (Imm64 v2)) /\
           v1 <+ v2 /\
           v1 + 44w <=+ v2 /\
           v2 <=+ v1 + 47w))
``,
  cheat
);







(*
"bir_backlifterTheory.bir_exec_to_labels_TO_exec_to_addr_label_n"
*)

bir_program_transfTheory.bir_step_n_in_L_IMP_exec_to_labels_thm

(*

TODO: establish relational postcondition

*)

val abstract_jgmt_rel_def = Define `
    abstract_jgmt_rel m (l:'a) (ls:'a->bool) pre post =
  !ms .
   ((m.pc ms) = l) ==> (pre ms) ==>
   ?ms'. ((m.weak ms ls ms') /\
    (post ms ms'))
`;


val bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm = prove (``
!bprog l L ls pre post.
(bir_step_n_in_L_jgmt
  bprog
  (bir_block_pc l)
  L
  pre
  post) ==>

(L INTER (IMAGE bir_block_pc ls) = EMPTY) ==>
(!st st'. post st st' ==> st'.bst_pc IN (IMAGE bir_block_pc ls)) ==>

(abstract_jgmt_rel
  (bir_etl_wm bprog)
  l
  ls
  pre
  post)
``,
  cheat
);


val bir_abstract_jgmt_rel_thm = prove(``
(abstract_jgmt_rel
  (bir_etl_wm bprog)
  (BL_Address (Imm32 2824w))
  {BL_Address (Imm32 2886w)}
  (\st.
       st.bst_status = BST_Running /\
       bir_envty_list_b birenvtyl st.bst_environ /\
       bir_eval_exp
         (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
               (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
               (BExp_Aligned Bit32 2
                  (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))) st.bst_environ =
       SOME bir_val_true)
  (\st st'.
         ?v1 v2.
           bir_env_lookup "countw" st.bst_environ =
           SOME (BVal_Imm (Imm64 v1)) /\
           bir_env_lookup "countw" st'.bst_environ =
           SOME (BVal_Imm (Imm64 v2)) /\
           v1 <+ v2 /\
           v1 + 44w <=+ v2 /\
           v2 <=+ v1 + 47w))
``,
  cheat
);

(*

TODO: transfer of relational postcondition to machine model

*)


(*
TODO: go to didrik style m0_mod weak transition relation
*)

val m_weak_trs_def = Define `
    m_weak_trs pcf stepf ms ls ms' = 
        ?n.
          ((n > 0) /\
           (FUNPOW_OPT stepf n ms = SOME ms') /\
           ((pcf ms') IN ls)
          ) /\
          !n'.
            (((n' < n) /\ (n' > 0)) ==>
            ?ms''.
              (FUNPOW_OPT stepf n' ms = SOME ms'') /\
              ((pcf ms'') NOTIN ls)
            )`;
val m_weak_model_def = Define `
    m_weak_model pcf bmr  = <|
    trs  := bmr.bmr_step_fun;
    weak := m_weak_trs pcf bmr.bmr_step_fun;
    pc   := pcf
  |>`;
val m0_mod_weak_trs_def = Define `
    m0_mod_weak_trs = m_weak_trs (\x. x.base.REG RName_PC) (m0_mod_bmr (T,T)).bmr_step_fun
`;
val m0_mod_weak_model_def = Define `
    m0_mod_weak_model = m_weak_model (\x. x.base.REG RName_PC) (m0_mod_bmr (T,T))
`;

val m_triple_rel_def = Define `
    m_triple_rel wm bmr mms l ls pre post =
    abstract_jgmt_rel wm l ls
      (\ms. (bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains bmr ms) mms) /\
            (pre ms))         
      (\ms ms'. (bmr.bmr_extra ms')  /\
            (EVERY (bmr_ms_mem_contains bmr ms') mms) /\
            (post ms ms'))
`;
val m0_mod_triple_rel_def = Define `
    m0_mod_triple_rel = m_triple m0_mod_weak_model (m0_mod_bmr (T,T))
`;

(* TODO: translate to pure Cortex-M0 property *)
(* =================================================================================== *)
(*
bir_backlifterTheory.bir_post_bir_to_arm8_def
lift_contract_thm
src/tools/backlifter/bir_backlifterLib.sml

get_arm8_contract_sing

examples/tutorial/7-composition/tutorial_backliftingScript.sml
*)
(* =================================================================================== *)

(* TODO: stolen and adjusted/generalized from "bir_backlifterTheory.bir_is_lifted_prog_MULTI_STEP_EXEC_compute" *)
(* =================================================================================== *)
val bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm =
  prove(
  ``!mu bs bs' ms mla (p:'a bir_program_t) (r:('c, 'd, 'b) bir_lifting_machine_rec_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog r mu mms p ==>
    bmr_rel r bs ms ==>
    MEM (BL_Address mla) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains r ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
    ?ms' li.
    (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
    bmr_ms_mem_unchanged r ms ms' mu /\
    EVERY (bmr_ms_mem_contains r ms') mms /\
    (bs'.bst_pc = bir_block_pc (BL_Address li)) /\
    MEM (BL_Address li) (bir_labels_of_program p) /\
    bmr_rel r bs' ms'
``,

REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:('c, 'd, 'b) bir_lifting_machine_rec_t``, ``mu:'c word_interval_t``,
                    ``mms:(('c word)# ('d word) list) list``,
                    ``p:'a bir_program_t``] bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
bir_auxiliaryLib.QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_state_is_terminated_def]
);

val bir_is_lifted_prog_MULTI_STEP_EXEC_compute_32_8_thm =
  INST_TYPE
    [Type.gamma |-> ``:32``, Type.delta |-> ``:8``]
    bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm;
(* =================================================================================== *)


(*

TODO: this is probably in precondition lifting
"bir_backlifterTheory.exist_bir_of_arm8_thm"
bir_backlifterTheory.bir_pre_arm8_to_bir_def
bir_backlifterTheory.bir_post_bir_to_arm8_def
((
!ms.
?bs.
  (bir_envty_list_b birenvtyl st.bst_environ) /\
  bmr_rel (m0_mod_bmr (T,T)) bs ms
))
bir_lifting_machinesTheory.m0_mod_bmr_def



((
``
!bprog bs n L bs'.
(step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  ?n' lo.
  (bir_exec_to_addr_label_n bprog bs n' = BER_Ended lo n n' bs')
``
))
*)




val lift_contract_thm = store_thm(
   "lift_contract_thm", ``
!mla.
  bir_is_lifted_prog (m0_mod_bmr (T,T)) mu mms p ==>
  (MEM (BL_Address mla) (bir_labels_of_program bprog)) ==>

  (abstract_jgmt_rel
    (bir_etl_wm bprog)
    (BL_Address (Imm32 l))
    (IMAGE (\x. (BL_Address (Imm32 x))) ls)
    (bpre)
    (bpost)) ==>

  (abstract_jgmt_rel
    m0_mod_weak_model
    l
    ls
    (m0_mod_pre)
    (m0_mod_post))
``,
  cheat
);


(*

TODO: transfer to (unmodified) m0 model

*)



val _ = print_term (concl bprog_bir_prop_thm);
