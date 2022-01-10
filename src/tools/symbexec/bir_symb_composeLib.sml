structure bir_symb_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_composeLib"
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


val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in

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

val birs_states_mid = (pred_setSyntax.strip_set o snd o dest_eq o concl o birs_exec_step_CONV) test_term;
val birs_state_mid = List.nth(birs_states_mid,0);
val test_term_mid = ``birs_exec_step ^bprog ^birs_state_mid``;
val _ = (print_term o concl) (birs_exec_step_CONV test_term_mid);

val birs_state_mid_lbl = (snd o dest_eq o concl o EVAL) ``(^birs_state_mid).bsst_pc``;

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

val birs_symb_symbst_pc_thm = store_thm(
   "birs_symb_symbst_pc_thm", ``
!s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
);


(* first step *)
val symb_state = ``birs_symb_to_symbst ^birs_state_init``;
val lbls = ``{^birs_state_init_lbl}``;

val A_single_step_prog_thm =
  SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss++HolBACoreSimps.holBACore_ss)
    [birs_symb_symbst_pc_thm, pred_setTheory.IN_SING]
    (REWRITE_RULE [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_exec_step_CONV test_term]
       (SPECL [symb_state, lbls] birs_rule_STEP_thm));
val (_,[_,A_sysLPi_tm]) = 
  (strip_comb o concl) A_single_step_prog_thm;
val [A_sys_tm, A_L_tm, A_Pi_tm] =
  pairSyntax.strip_pair A_sysLPi_tm;


(* second step *)
val symb_state = ``birs_symb_to_symbst ^birs_state_mid``;
val lbls = ``{^birs_state_mid_lbl}``;

val B_single_step_prog_thm =
  SIMP_RULE (std_ss++symb_typesLib.symb_TYPES_ss++birs_state_ss++HolBACoreSimps.holBACore_ss)
    [birs_symb_symbst_pc_thm, pred_setTheory.IN_SING]
    (REWRITE_RULE [bir_symbTheory.birs_symb_to_from_symbst_thm, birs_exec_step_CONV test_term_mid]
       (SPECL [symb_state, lbls] birs_rule_STEP_thm));
val (_,[_,B_sysLPi_tm]) = 
  (strip_comb o concl) B_single_step_prog_thm;
val [B_sys_tm, B_L_tm, B_Pi_tm] =
  pairSyntax.strip_pair B_sysLPi_tm;

(* now the composition *)

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_rule_SEQ_thm =
  (MATCH_MP symb_rulesTheory.symb_rule_SEQ_thm birs_symb_symbols_f_sound_prog_thm);



val symb_symbols_set_ALT_thm = store_thm(
   "symb_symbols_set_ALT_thm", ``
!sr Pi.
  symb_symbols_set sr Pi = (BIGUNION (IMAGE (symb_symbols sr) Pi))
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_def, IMAGE_DEF]
);

val birs_symb_symbols_set_EQ_thm = store_thm(
   "birs_symb_symbols_set_EQ_thm", ``
!prog Pi.
  symb_symbols_set (bir_symb_rec_sbir prog) (IMAGE birs_symb_to_symbst Pi) = BIGUNION (IMAGE birs_symb_symbols Pi)
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_ALT_thm, EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [IN_BIGUNION_IMAGE] >>
  FULL_SIMP_TAC (std_ss) [IN_IMAGE] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm]
  )
);

val birs_exps_of_senv_def = Define `
    birs_exps_of_senv senv =
      {e | (?vn. senv vn = SOME e)}
`;

val birs_exps_of_senv_COMP_def = Define `
    birs_exps_of_senv_COMP excset senv =
      {e | (?vn. (~(vn IN excset)) /\ senv vn = SOME e)}
`;

val birs_exps_of_senv_thm = store_thm(
   "birs_exps_of_senv_thm", ``
!senv.
  birs_exps_of_senv senv
  =
  birs_exps_of_senv_COMP EMPTY senv
``,
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def, birs_exps_of_senv_def]
);

val birs_exps_of_senv_COMP_thm = store_thm(
   "birs_exps_of_senv_COMP_thm", ``
!sr Pi.
  (!excset. birs_exps_of_senv_COMP excset (K NONE) = EMPTY) /\
  (!excset senv vn sv. birs_exps_of_senv_COMP excset ((vn =+ (SOME sv)) senv) =
    if vn IN excset then
      birs_exps_of_senv_COMP (vn INSERT excset) senv
    else
      sv INSERT (birs_exps_of_senv_COMP (vn INSERT excset) senv)) /\
  (!excset senv vn. birs_exps_of_senv_COMP excset ((vn =+ NONE) senv) = (birs_exps_of_senv_COMP (vn INSERT excset) senv))
``,
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def]
  ) >>

  Cases_on `vn IN excset` >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [EXTENSION] >>
    REPEAT STRIP_TAC >> EQ_TAC >> (
      REPEAT STRIP_TAC >>
      METIS_TAC [combinTheory.APPLY_UPDATE_THM, optionTheory.option_CLAUSES]
    )
  )
);

val birs_symb_symbols_thm = store_thm(
   "birs_symb_symbols_thm", ``
!sys.
  birs_symb_symbols sys = (BIGUNION (IMAGE bir_vars_of_exp (birs_exps_of_senv sys.bsst_environ))) UNION (bir_vars_of_exp sys.bsst_pcond)
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def, IMAGE_DEF, birs_exps_of_senv_def, IN_GSPEC_IFF]
);

val freesymbols_thm = store_thm(
   "freesymbols_thm", ``
symb_symbols (bir_symb_rec_sbir ^bprog) ^A_sys_tm INTER
  (symb_symbols_set (bir_symb_rec_sbir ^bprog) ^B_Pi_tm DIFF
     symb_symbols (bir_symb_rec_sbir ^bprog) ^B_sys_tm)
= EMPTY
``,
  FULL_SIMP_TAC (std_ss) [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm, birs_symb_symbols_set_EQ_thm] >>
  FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >>
  FULL_SIMP_TAC (std_ss) [birs_symb_symbols_thm] >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] >>

  EVAL_TAC
(*
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.GSPECIFICATION]
*)
);

val bprog_composed_thm = save_thm(
   "bprog_composed_thm",
  MATCH_MP
    (MATCH_MP
       (MATCH_MP
          birs_rule_SEQ_thm
          freesymbols_thm)
    A_single_step_prog_thm)
    B_single_step_prog_thm
);

(* TODO: tidy up set operations *)

end (* local *)



end (* struct *)
