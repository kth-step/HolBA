
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
       pc.bpc_index = 0 /\
       bir_envty_list birenvtyl st /\
       bir_eval_exp ^bprecond (BEnv st) = SOME bir_val_true)
`;
(* translate the property to BIR state property *)
val bprog_P_thm = store_thm(
   "bprog_P_thm", ``
!bs.
  bprog_P (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bs.bst_pc.bpc_index = 0 /\
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
       (status2 = BST_Running /\
        ?v1 v2. (st1 "countw" = SOME (BVal_Imm (Imm64 v1))) /\
                (st2 "countw" = SOME (BVal_Imm (Imm64 v2))) /\
                (v1 <=+ 0xFFFFFFFFFFFFFF00w) /\
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
      (bs2.bst_status = BST_Running /\
       ?v1 v2. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v1)) /\
               bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 v2)) /\
               (v1 <=+ 0xFFFFFFFFFFFFFF00w) /\
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

val bir_frag_l_tm = ``<|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>``;
val bir_frag_l_ml_tm = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl o EVAL) ``(^bir_frag_l_tm).bpc_label``;

val bir_frag_l_exit_ml_tm = ``2886w:word32``;
val bir_frag_l_exit_tm = ``<|bpc_label := BL_Address (Imm32 ^bir_frag_l_exit_ml_tm); bpc_index := 0|>``;

val bprecond_def = Define `
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
`;

val pre_bir_def = Define `
    pre_bir bs =
       (bir_eval_exp bprecond bs.bst_environ = SOME bir_val_true)
`;

val post_bir_def = Define `
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
`;

val pre_bir_nL_def = Define `
    pre_bir_nL st =
      (
       st.bst_status = BST_Running /\
       st.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl st.bst_environ /\

       pre_bir st
      )
`;
val post_bir_nL_def = Define `
    post_bir_nL (st:bir_state_t) st' =
      (
         (st'.bst_pc = ^bir_frag_l_exit_tm) /\
         st'.bst_status = BST_Running /\

         post_bir st st'
      )
`;

val bir_step_n_in_L_jgmt_thm = prove(``
bir_step_n_in_L_jgmt
  ^bprog_tm
  ^bir_frag_l_tm
  motor_analysis_L
  pre_bir_nL
  post_bir_nL
``,
  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  REWRITE_TAC [pre_bir_nL_def, pre_bir_def, bprecond_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPEC `st` bprog_bir_prop_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [prove(``(\x. bir_exec_step_state ^(bprog_tm) x) = bir_exec_step_state ^(bprog_tm)``, cheat)] >>
  Q.EXISTS_TAC `n` >>
  Q.EXISTS_TAC `st'` >>
  ASM_SIMP_TAC std_ss [] >>

  REWRITE_TAC [post_bir_nL_def, post_bir_def] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []
);


val motor_analysis_L_INTER_thm = prove(``
motor_analysis_L INTER
        {<|bpc_label := BL_Address (Imm32 2886w); bpc_index := 0|>} =
        EMPTY
``,
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
);

val bir_abstract_jgmt_rel_motor_thm = prove(``
abstract_jgmt_rel
  (bir_etl_wm ^bprog_tm)
  (BL_Address (Imm32 ^bir_frag_l_ml_tm))
  {BL_Address (Imm32 ^bir_frag_l_exit_ml_tm)}
  pre_bir_nL
  post_bir_nL
``,
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
);

val bmemms_t = List.nth((snd o strip_comb o concl) bin_motor_funcTheory.bin_motor_func_thm, 2);
val bmemms_def = Define `
    bmemms = ^(bmemms_t)
`;
val bin_motor_func_thm = REWRITE_RULE [GSYM bmemms_def, GSYM bprog_def] bin_motor_funcTheory.bin_motor_func_thm;


(* TODO: COPIED STUFF *)
(* =================================================================================== *)
val bmr_rel_m0_mod_bmr_IMP_index_thm = prove(``
!ms bs.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bs.bst_status = BST_Running) ==>
  (bs.bst_pc.bpc_index = 0)
``,
  EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  )
);

val bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm = prove(``
!bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "countw" bs.bst_environ = SOME (BVal_Imm (Imm64 ms.countw)))
``,
  EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
);

val bmr_rel_m0_mod_bmr_IMP_SP_process_lookup_thm = prove(``
!bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "SP_process" bs.bst_environ = SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_process))))
``,
  EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
);
(* =================================================================================== *)

(*
  transfer of relational postcondition to machine model
*)
val pre_m0_mod_def = Define `
    pre_m0_mod ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms) bmemms) /\
        ((m0_mod_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.base.REG RName_SP_process /\
         ms.base.REG RName_SP_process && 0x3w = 0w /\
         ms.countw <=+ 0xFFFFFFFFFFFFFF00w)
      )
`;
val post_m0_mod_def = Define `
    post_m0_mod ms ms' =
      (
        (ms.countw <=+ 0xFFFFFFFFFFFFFF00w) /\
        (ms.countw + 44w <=+ ms'.countw) /\
        (ms'.countw <=+ ms.countw + 47w)
      )
`;

val backlift_bir_m0_mod_pre_abstr_ex_thm = prove(``
  backlift_bir_m0_mod_pre_abstr pre_m0_mod pre_bir_nL
``,
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
);

val backlift_bir_m0_mod_post_concr_ex_thm = prove(``
  backlift_bir_m0_mod_post_concr post_bir_nL post_m0_mod
``,
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
);

val m0_mod_thm = prove(``
abstract_jgmt_rel
  m0_mod_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  pre_m0_mod
  post_m0_mod
``,

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
);


(* TODO: MORE COPIED STUFF *)
(* =================================================================================== *)
val m0_mod_R_IMP_bmr_ms_mem_contains_thm = prove(``
!mms ms.
  (m0_mod_R ms mms) ==>
  (bmr_ms_mem_contains (m0_mod_bmr (F,T)) mms =
   bmr_ms_mem_contains (m0_bmr (F,T)) ms)
``,
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
);
val m0_mod_R_IMP_REG_EQ_thm = prove(``
!mms ms.
  (m0_mod_R ms mms) ==>
  (mms.base.REG = ms.REG)
``,
  REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
);
val m0_mod_R_IMP_bmr_extra_thm = prove(``
!mms ms.
  (m0_mod_R ms mms) ==>
  ((m0_mod_bmr (F,T)).bmr_extra mms = (m0_bmr (F,T)).bmr_extra ms)
``,
  REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.m0_mod_state_is_OK_def, bir_lifting_machinesTheory.m0_state_is_OK_def] >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
);
val m0_mod_R_IMP_count_EQ_countw_thm = prove(``
!mms ms.
  (m0_mod_R ms mms) ==>
  (ms.count = w2n mms.countw)
``,
  REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
);

(* =================================================================================== *)

(*
transfer to (unmodified) m0 model
*)

val pre_m0_def = Define `
    pre_m0 ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_bmr (F,T)) ms) bmemms) /\
        ((m0_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.REG RName_SP_process /\
         ms.REG RName_SP_process && 0x3w = 0w /\
         ms.count <= 0xFFFFFFFFFFFFFF00:num)
      )
`;
val post_m0_def = Define `
    post_m0 ms ms' =
      (
        (ms.count + 44 <= ms'.count) /\
        (ms'.count <= ms.count + 47)
      )
`;



val backlift_m0_mod_m0_pre_abstr_ex_thm = prove(``
  backlift_m0_mod_m0_pre_abstr (pre_m0) (pre_m0_mod)
``,
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
);

val backlift_m0_mod_m0_post_concr_ex_thm = prove(``
  backlift_m0_mod_m0_post_concr post_m0_mod post_m0
``,
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
);

val m0_thm = store_thm(
   "m0_thm", ``
abstract_jgmt_rel
  m0_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  (pre_m0)
  (post_m0)
``,

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
);

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
