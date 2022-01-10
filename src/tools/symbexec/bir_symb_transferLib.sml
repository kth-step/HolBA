structure bir_symb_transferLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_transferLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  open bir_symbLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open bir_symb_composeLib;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in

(* testing *)
val bprog_test_def = Define `
    bprog_test =
BirProgram [
           <|bb_label := BL_Address (Imm32 2826w);
             bb_statements :=
               [BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
`;
val bprog = (fst o dest_eq o concl) bprog_test_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 2826w))``;
val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := ("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ));
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;

val test_term = ``birs_exec_step ^bprog ^birs_state_init``;
val _ = (print_term o concl) (birs_exec_step_CONV test_term);

val bir_prog_has_no_halt_prog_thm = store_thm(
   "bir_prog_has_no_halt_prog_thm", ``
bir_prog_has_no_halt bprog_test
``,
  EVAL_TAC
);
val birs_symb_step_sound_prog_thm =
  MP
    (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_step_sound_thm)
    bir_prog_has_no_halt_prog_thm;

val birs_rule_STEP_thm =
  SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss) []
  (REWRITE_RULE [Once bir_symbTheory.bir_symb_rec_sbir_def]
     (MATCH_MP symb_rulesTheory.symb_rule_STEP_thm birs_symb_step_sound_prog_thm));

val symb_state = ``birs_symb_to_symbst ^birs_state_init``;
val lbls = ``{^birs_state_init_lbl}``;


val birs_symb_symbst_pc_thm = store_thm(
   "birs_symb_symbst_pc_thm", ``
!s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
);

val single_step_prog_thm =
  SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss++HolBACoreSimps.holBACore_ss)
    [birs_symb_symbst_pc_thm, pred_setTheory.IN_SING]
    (REWRITE_RULE [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_exec_step_CONV test_term]
       (SPECL [symb_state, lbls] birs_rule_STEP_thm));
val (_,[_,sysLPi_tm]) = 
  (strip_comb o concl) single_step_prog_thm;
val [sys_tm, L_tm, Pi_tm] =
  pairSyntax.strip_pair sysLPi_tm;

(* now the transfer *)

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);

val bprog_P_def = Define `
    bprog_P ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       (?v_R7. st "R7" = SOME v_R7 /\ type_of_bir_val v_R7 = BType_Imm Bit32) /\
       (?v_SP_process. st "SP_process" = SOME v_SP_process /\ type_of_bir_val v_SP_process = BType_Imm Bit32) /\
       (?v_countw. st "countw" = SOME v_countw /\ type_of_bir_val v_countw = BType_Imm Bit64) /\
       (!vn. vn <> "R7" ==> vn <> "SP_process" ==> vn <> "countw" ==> st vn = NONE))
`;

(* this is the relevant property about the cycle counter *)
val bprog_Q_def = Define `
    bprog_Q
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (?v. st1 "countw" = SOME (BVal_Imm (Imm64 v)) /\ st2 "countw" = SOME (BVal_Imm (Imm64 (v + 1w))))
`;
val bprog_Q_thm = store_thm(
   "bprog_Q_thm", ``
!bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (?v. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v)) /\
         bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 (v + 1w))))
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
);

val string_ss = rewrites (type_rws ``:string``);
val bprog_P_entails_thm = store_thm(
   "bprog_P_entails_thm", ``
P_entails_an_interpret (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm
``,
  FULL_SIMP_TAC (std_ss++birs_state_ss) [P_entails_an_interpret_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_EQ_thm] >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_to_symbst_def, symb_symbst_pc_def] >>

  Cases_on `s` >> Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_typesLib.symb_TYPES_ss) [bprog_P_def, birs_symb_to_concst_def, symb_concst_pc_def] >>

  Q.EXISTS_TAC `SymbInterpret
    ((BVar "sy_R7" (BType_Imm Bit32) =+ SOME v_R7)
    ((BVar "sy_SP_process" (BType_Imm Bit32) =+ SOME v_SP_process)
    ((BVar "sy_countw" (BType_Imm Bit64) =+ SOME v_countw) (K NONE))))` >>

  FULL_SIMP_TAC (std_ss) [birs_symb_matchstate_def] >>

  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) []
  ) >- (
    FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def] >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_dom_def, birs_symb_symbols_def, bir_typing_expTheory.bir_vars_of_exp_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.SUBSET_DEF] >>
    REPEAT STRIP_TAC >>
    Cases_on `vn = "countw"` >> Cases_on `vn = "SP_process"` >> Cases_on `vn = "R7"` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss) [combinTheory.APPLY_UPDATE_THM] >>
      PAT_X_ASSUM ``BExp_Den A = B`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_SING] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss++string_ss) []
    )
  ) >- (
    FULL_SIMP_TAC (std_ss) [birs_interpr_welltyped_def] >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_dom_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    REPEAT STRIP_TAC >>
    Cases_on `sy = BVar "sy_countw" (BType_Imm Bit64)` >> Cases_on `sy = BVar "sy_SP_process" (BType_Imm Bit32)` >> Cases_on `sy = BVar "sy_R7" (BType_Imm Bit32)` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss++holBACore_ss) [symb_interpr_get_def, combinTheory.APPLY_UPDATE_THM]
    )
  ) >- (
    FULL_SIMP_TAC (std_ss) [birs_matchenv_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `var = "countw"` >> Cases_on `var = "SP_process"` >> Cases_on `var = "R7"` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss) [combinTheory.APPLY_UPDATE_THM] >>
      REWRITE_TAC [birs_interpret_fun_thm] >>
      EVAL_TAC
    ) >>
    METIS_TAC []
  ) >>

  EVAL_TAC
);

val bprog_Pi_overapprox_Q_thm = store_thm(
   "bprog_Pi_overapprox_Q_thm", ``
Pi_overapprox_Q (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm ^Pi_tm bprog_Q
``,
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
(*           val _ = print_term tm; *)
           val conv = SIMP_CONV std_ss [birs_symb_symbols_thm] THENC SIMP_CONV (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] THENC EVAL;
           val thm_res = conv tm;
(*           val _ = print_term (concl thm_res); *)
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

val bprog_prop_holds_thm =
  MATCH_MP
    (MATCH_MP
      (MATCH_MP
         birs_prop_transfer_thm
         bprog_P_entails_thm)
      bprog_Pi_overapprox_Q_thm)
    single_step_prog_thm;
val bprog_concst_prop_thm =
  SIMP_RULE (std_ss++birs_state_ss)
    [birs_symb_symbst_pc_thm]
    (REWRITE_RULE
      [symb_prop_transferTheory.prop_holds_def]
      bprog_prop_holds_thm);

(* TODO: translate to pure BIR property *)


end (* local *)

end (* struct *)
