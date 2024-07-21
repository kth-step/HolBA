open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open isqrtTheory;
open isqrt_specTheory;
open isqrt_symb_execTheory;

val _ = new_theory "isqrt_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

(* before loop contract *)

val init_addr_1_tm = (snd o dest_eq o concl) isqrt_init_addr_1_def;
val end_addr_1_tm = (snd o dest_eq o concl) isqrt_end_addr_1_def;

val bspec_pre_1_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_pre_1_def;
val bspec_post_1_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_post_1_def;

val bspec_cont_1_thm =
 bir_symb_transfer init_addr_1_tm end_addr_1_tm bspec_pre_1_tm bspec_post_1_tm
  bir_isqrt_prog_def isqrt_birenvtyl_def
  bspec_isqrt_pre_1_def bspec_isqrt_post_1_def isqrt_prog_vars_list_def
  isqrt_symb_analysis_1_thm isqrt_bsysprecond_1_thm isqrt_prog_vars_thm;

Theorem bspec_cont_isqrt_1:
 bir_cont bir_isqrt_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_1_tm)) {BL_Address (Imm64 ^end_addr_1_tm)} {}
  ^bspec_pre_1_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_1_tm)
       then ^bspec_post_1_tm
       else bir_exp_false)
Proof
 rw [bir_isqrt_prog_def,bspec_cont_1_thm]
QED

(* loop body contract *)

val init_addr_2_tm = (snd o dest_eq o concl) isqrt_init_addr_2_def;
val end_addr_2_tm = (snd o dest_eq o concl) isqrt_end_addr_2_def;

val bspec_pre_2_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_pre_2_def;
val bspec_post_2_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_post_2_def;

val bspec_cont_2_thm =
 bir_symb_transfer init_addr_2_tm end_addr_2_tm bspec_pre_2_tm bspec_post_2_tm
  bir_isqrt_prog_def isqrt_birenvtyl_def
  bspec_isqrt_pre_2_def bspec_isqrt_post_2_def isqrt_prog_vars_list_def
  isqrt_symb_analysis_2_thm isqrt_bsysprecond_2_thm isqrt_prog_vars_thm;

Theorem bspec_cont_isqrt_2:
 bir_cont bir_isqrt_prog bir_exp_true
  (BL_Address (Imm64 ^init_addr_2_tm)) {BL_Address (Imm64 ^end_addr_2_tm)} {}
  ^bspec_pre_2_tm
  (\l. if l = BL_Address (Imm64 ^end_addr_2_tm)
       then ^bspec_post_2_tm
       else bir_exp_false)
Proof
 rw [bir_isqrt_prog_def,bspec_cont_2_thm]
QED

(* branch contract *)

val init_addr_tm = (snd o dest_eq o concl) isqrt_init_addr_3_def;
val end_addr_1_tm = (snd o dest_eq o concl) isqrt_end_addr_3_loop_def;
val end_addr_2_tm = (snd o dest_eq o concl) isqrt_end_addr_3_ret_def;

val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_pre_3_def;
val bspec_post_1_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_post_3_loop_def;
val bspec_post_2_tm = (lhs o snd o strip_forall o concl) bspec_isqrt_post_3_ret_def;

val bir_prog_def = bir_isqrt_prog_def;
val birenvtyl_def = isqrt_birenvtyl_def;
val bspec_pre_def = bspec_isqrt_pre_3_def;
val bspec_post_1_def = isqrt_end_addr_3_loop_def;
val bspec_post_2_def = isqrt_end_addr_3_ret_def;
val prog_vars_list_def = isqrt_prog_vars_list_def;
val symb_analysis_thm = isqrt_symb_analysis_3_thm;
val bsysprecond_thm = isqrt_bsysprecond_3_thm;
val prog_vars_thm = isqrt_prog_vars_thm;

(* ---- *)

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open HolBACoreSimps;
open bir_typing_expTheory;

open pred_setTheory;
open distribute_generic_stuffTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
val bprog_tm = (fst o dest_eq o concl) bir_prog_def;
val prog_vars_list_tm = (fst o dest_eq o concl) prog_vars_list_def;
val birenvtyl_tm = (fst o dest_eq o concl) birenvtyl_def;
val bir_state_init_lbl_tm = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;

val birs_state_end_lbl_1_tm = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_1_tm))``;
val birs_state_end_lbl_2_tm = (snd o dest_eq o concl o EVAL)
 ``bir_block_pc (BL_Address (Imm64 ^end_addr_2_tm))``;

val birs_state_init_pre_tm =
``birs_state_init_pre_GEN ^bir_state_init_lbl_tm ^birenvtyl_tm
  (mk_bsysprecond ^bspec_pre_tm ^birenvtyl_tm)``;

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) symb_analysis_thm;

Theorem analysis_L_INTER_EMPTY[local]:
 {^birs_state_end_lbl_1_tm; ^birs_state_end_lbl_2_tm} INTER ^L_s = {}
Proof
 EVAL_TAC
QED

val birs_state_init_pre_EQ_thm =
  prove (``^((snd o dest_comb) sys_i) = ^birs_state_init_pre_tm``,
   REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, bsysprecond_thm] >>
   CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV));

val analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm, GSYM bir_prog_def] symb_analysis_thm;

val birenvtyl_EVAL_thm =
 (REWRITE_CONV [
     birenvtyl_def,
     bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
     bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL)
   birenvtyl_tm;

val birs_state_thm = REWRITE_CONV [birenvtyl_EVAL_thm] birs_state_init_pre_tm;

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm)
    bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm
    birs_symb_symbols_f_sound_prog_thm);

val type_of_bir_exp_thms =
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      open bir_interval_expTheory
    in [
      type_of_bir_exp_def,
      bir_var_type_def,
      bir_type_is_Imm_def,
      type_of_bir_imm_def,
      BExp_Aligned_type_of,
      BExp_unchanged_mem_interval_distinct_type_of,
      bir_number_of_mem_splits_REWRS,
      BType_Bool_def,
      bir_exp_true_def,
      bir_exp_false_def,
      BExp_MSB_type_of,
      BExp_nzcv_ADD_DEFS,
      BExp_nzcv_SUB_DEFS,
      n2bs_def,
      BExp_word_bit_def,
      BExp_Align_type_of,
      BExp_ror_type_of,
      BExp_LSB_type_of,
      BExp_word_bit_exp_type_of,
      BExp_ADD_WITH_CARRY_type_of,
      BExp_word_reverse_type_of,
      BExp_ror_exp_type_of
    ] end;

val bprog_P_entails_thm =
 prove (``P_entails_an_interpret
  (bir_symb_rec_sbir ^bprog_tm)
  (P_bircont ^birenvtyl_tm ^bspec_pre_tm)
  (birs_symb_to_symbst ^birs_state_init_pre_tm)``,

 ASSUME_TAC (GSYM prog_vars_thm) >>
 `^prog_vars_list_tm = MAP PairToBVar ^birenvtyl_tm` by (
  SIMP_TAC std_ss [birenvtyl_def, listTheory.MAP_MAP_o,
   PairToBVar_BVarToPair_I_thm, listTheory.MAP_ID]) >>
 POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
 IMP_RES_TAC (SIMP_RULE std_ss [] P_bircont_entails_thm) >>
 SIMP_TAC std_ss [] >>
 POP_ASSUM (ASSUME_TAC o SPEC bspec_pre_tm) >>
 `bir_vars_of_exp ^bspec_pre_tm SUBSET set (MAP PairToBVar ^birenvtyl_tm)` by EVAL_TAC >>
 POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
 `ALL_DISTINCT (MAP FST ^birenvtyl_tm)` by EVAL_TAC >>
 POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
 `IS_SOME (type_of_bir_exp ^bspec_pre_tm)` by (
   SIMP_TAC std_ss [bspec_pre_def] >>
   CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) type_of_bir_exp_thms)) >>
   SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES]
 ) >>
 POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]));

val sys1 = (snd o dest_eq o concl o REWRITE_CONV [bsysprecond_thm]) birs_state_init_pre_tm;

val (Pi_func, Pi_set) = dest_comb Pi_f;

val sys2s = pred_setSyntax.strip_set Pi_set;

val sys2s_posts = [];

val label_0 = (snd o dest_eq o concl o EVAL) `` ^(List.nth (sys2s,0)).bsst_pc``;
val label_1 = (snd o dest_eq o concl o EVAL) `` ^(List.nth (sys2s,1)).bsst_pc``;

val _ = export_theory ();
