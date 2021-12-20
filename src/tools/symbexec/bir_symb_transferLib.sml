structure bir_symb_transferLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_transferLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  open bir_symbLib;

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

val birs_symb_step_sound_prog_thm =
  (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_step_sound_thm);

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
    bprog_P (s:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      T
`;

(* TODO: add the relevant property about the cycle counter *)
val bprog_Q_def = Define `
    bprog_Q
     (s1:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     (s2:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     T
`;

val bprog_P_entails_thm = store_thm(
   "bprog_P_entails_thm", ``
P_entails_an_interpret (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm
``,
  cheat
);

val bprog_Pi_overapprox_Q_thm = store_thm(
   "bprog_Pi_overapprox_Q_thm", ``
Pi_overapprox_Q (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm ^Pi_tm bprog_Q
``,
  cheat
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
