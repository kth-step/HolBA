
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

(* testing *)
val bprog_test_def = Define `
    bprog_test =
BirProgram [
           <|bb_label := BL_Address (Imm32 2826w);
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)));
                BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
`;
val bprog = (fst o dest_eq o concl) bprog_test_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_pc_next (bir_block_pc (BL_Address (Imm32 2826w)))``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_pc_next (^birs_state_init_lbl)``;


val m0_mod_vars_def = Define `
    m0_mod_vars = bmr_vars (m0_mod_bmr (T,T))
`;

val m0_mod_vars_thm = store_thm(
   "m0_mod_vars_thm", ``
!ef sel.
  m0_mod_vars = bmr_vars (m0_mod_bmr (ef,sel))
``,
  METIS_TAC [m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL]
);

val birenvtyl_def = Define `
    birenvtyl = MAP BVarToPair m0_mod_vars
`;
(*    birenvtyl = [("R7", BType_Imm Bit32); ("SP_process", BType_Imm Bit32); ("countw", BType_Imm Bit64)]*)
(*
bir_lifting_machinesTheory.m0_mod_REGS_lifted_imms_LIST_def
m0_mod_REGS_lifted_imms_LIST
m0_mod_lifted_mem
bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL
*)
val birenvtyl_EVAL_thm = save_thm(
   "birenvtyl_EVAL_thm",
  (REWRITE_CONV [birenvtyl_def, m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL] THENC EVAL) ``birenvtyl``
);

(*
    ``bprecond = BExp_Const (Imm1 1w)``
*)
val bprecond_def = Define `
    bprecond = BExp_BinPred BIExp_Equal (BExp_Den (BVar "R0" (BType_Imm Bit32))) (BExp_Den (BVar "R1" (BType_Imm Bit32)))
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

val birs_state_init_pre = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := ^bsysprecond
|>``;
val birs_state_thm = REWRITE_CONV [birenvtyl_EVAL_thm] birs_state_init_pre;
val birs_state_init = (snd o dest_eq o concl) birs_state_thm;
(* ........................... *)

val bprog_tm = bprog;
val birs_rule_STEP_thm = birs_rule_STEP_prog_fun bprog_tm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_fun_spec = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm;
(* ........................... *)

(* first step *)
val single_step_thm = birs_rule_STEP_fun_spec birs_state_init;

val exec_thm = single_step_thm;
val (sys_tm, L_tm, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) exec_thm;
(* ........................... *)

(* now the transfer *)
(* ........................... *)

(* prepare property transfer theorem *)
val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

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
       (?v. st1 "countw" = SOME (BVal_Imm (Imm64 v)) /\ st2 "countw" = SOME (BVal_Imm (Imm64 (v + 1w))))
     )
`;
val bprog_Q_thm = store_thm(
   "bprog_Q_thm", ``
!bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = ^birs_state_end_lbl)
      /\
      (?v. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v)) /\
           bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 (v + 1w))))
    )
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
);
(* ........................... *)

(* P is generic enough *)

val bprog_P_entails_thm = store_thm(
   "bprog_P_entails_thm", ``
P_entails_an_interpret (bir_symb_rec_sbir ^bprog) bprog_P ^sys_tm
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
Pi_overapprox_Q (bir_symb_rec_sbir ^bprog) bprog_P ^sys_tm ^Pi_tm bprog_Q
``,
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

val tm2 = ``birs_exps_of_senv_COMP ∅
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
val tm2 = ``birs_exps_of_senv_COMP ∅
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
    single_step_thm;

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
    [bprog_P_thm, bprecond_def, bprog_Q_thm, birs_symb_concst_pc_thm, combinTheory.o_DEF, GSYM bir_programTheory.bir_exec_step_state_def]
    (REWRITE_RULE
      []
      bprog_to_concst_prop_thm)
);
(* ........................... *)




(* TODO: translate to pure Cortex-M0 property *)
(*
bir_backlifterTheory.bir_post_bir_to_arm8_def
lift_contract_thm
src/tools/backlifter/bir_backlifterLib.sml

get_arm8_contract_sing

examples/tutorial/7-composition/tutorial_backliftingScript.sml
*)

val _ = print_term (concl bprog_bir_prop_thm);
