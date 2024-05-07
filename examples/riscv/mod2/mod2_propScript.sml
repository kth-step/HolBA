open HolKernel boolLib Parse bossLib;

open numTheory arithmeticTheory int_bitwiseTheory;
open pairTheory combinTheory wordsTheory;

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

open program_logicSimps;

open mod2Theory;

open mod2_symb_execTheory;

open distribute_generic_stuffTheory;

val _ = new_theory "mod2_prop";

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_mod2_pre_def:
 riscv_mod2_pre x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w x)
End

Definition riscv_mod2_post_def:
 riscv_mod2_post x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w (x MOD 2))
End

(* ------------ *)
(* BIR contract *)
(* ------------ *)

Definition bir_mod2_pre_def:
  bir_mod2_pre x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w x)))
End

Definition bir_mod2_post_def:
 bir_mod2_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w (x MOD 2))))
End

val bir_mod2_pre = ``bir_mod2_pre``;
val bir_mod2_post = ``bir_mod2_post``;

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem mod2_riscv_pre_imp_bir_pre_thm[local]:
 bir_pre_riscv_to_bir (riscv_mod2_pre pre_x10) (bir_mod2_pre pre_x10)
Proof
 cheat
QED

Theorem mod2_riscv_post_imp_bir_post_thm[local]:
 !ls. bir_post_bir_to_riscv (riscv_mod2_post pre_x10) (\l. bir_mod2_post pre_x10) ls
Proof
 cheat
QED

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) mod2_symb_analysis_thm;

Definition incr_analysis_L_def:
 incr_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 4w))``;

Theorem mod2_analysis_L_NOTIN_thm[local]:
  (^birs_state_end_lbl) NOTIN incr_analysis_L
Proof
  EVAL_TAC
QED

(* ........................... *)
(* ........................... *)
(* ........................... *)

val birs_state_init_pre = ``birs_state_init_pre_GEN ^birs_state_init_lbl mod2_birenvtyl (mk_bsysprecond (bir_mod2_pre pre_x10) mod2_birenvtyl)``;

val mod2_bsysprecond_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV) ``mk_bsysprecond (bir_mod2_pre pre_x10) mod2_birenvtyl``;

Theorem birs_state_init_pre_EQ_thm:
  ^((snd o dest_comb) sys_i) = ^birs_state_init_pre
Proof
  REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, mod2_bsysprecond_thm] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
QED

val mod2_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm, GSYM bir_mod2_prog_def] mod2_symb_analysis_thm;

Theorem mod2_birenvtyl_EVAL_thm =
 (REWRITE_CONV [mod2_birenvtyl_def,
   bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
   bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL)
 ``mod2_birenvtyl``;

val birs_state_thm = REWRITE_CONV [mod2_birenvtyl_EVAL_thm] birs_state_init_pre;

(* ------ *)

(* now the transfer *)

val bprog_tm = (fst o dest_eq o concl) bir_mod2_prog_def;

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);

Definition bprog_P_def:
  bprog_P x = P_bircont mod2_birenvtyl (^bir_mod2_pre x)
End

Definition bprog_Q_def:
  bprog_Q x = Q_bircont (^birs_state_end_lbl) (set mod2_prog_vars) (^bir_mod2_post x)
End

Definition pre_bir_nL_def:
  pre_bir_nL x = pre_bircont_nL mod2_birenvtyl (^bir_mod2_pre x)
End

Definition post_bir_nL_def:
  post_bir_nL x = post_bircont_nL (^birs_state_end_lbl) (set mod2_prog_vars) (^bir_mod2_post x)
End
(* ........................... *)

(* P is generic enough *)
(* taken from "bir_exp_to_wordsLib" *)
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

Theorem bprog_P_entails_thm[local]:
  P_entails_an_interpret (bir_symb_rec_sbir ^bprog_tm) (bprog_P pre_x10) (birs_symb_to_symbst ^birs_state_init_pre)
Proof
  ASSUME_TAC (GSYM mod2_prog_vars_thm) >>
  `mod2_prog_vars = MAP PairToBVar mod2_birenvtyl` by (
    SIMP_TAC std_ss [mod2_birenvtyl_def, listTheory.MAP_MAP_o, PairToBVar_BVarToPair_I_thm, listTheory.MAP_ID]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  IMP_RES_TAC (SIMP_RULE std_ss [] P_bircont_entails_thm) >>

  SIMP_TAC std_ss [bprog_P_def] >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `bir_mod2_pre pre_x10`) >>
  `bir_vars_of_exp (bir_mod2_pre pre_x10) SUBSET set (MAP PairToBVar mod2_birenvtyl)` by (
    PAT_X_ASSUM ``A = set B`` (fn thm => REWRITE_TAC [GSYM thm]) >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_mod2_pre_def, bir_mod2_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM mod2_prog_vars_thm, mod2_prog_vars_def, bir_mod2_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  `ALL_DISTINCT (MAP FST mod2_birenvtyl)` by (
    SIMP_TAC (std_ss++listSimps.LIST_ss) [mod2_birenvtyl_EVAL_thm]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  `IS_SOME (type_of_bir_exp (bir_mod2_pre pre_x10))` by (
    SIMP_TAC std_ss [bir_mod2_pre_def, bir_mod2_pre_def] >>
    CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) type_of_bir_exp_thms)) >>
    SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm])
QED

(* ........................... *)
(* proof for each end state individually: *)

(* -------------------- *)

Theorem bir_cont_mod2[local]:
 bir_cont bir_mod2_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_mod2_pre pre_x10)
   (\l. if l = BL_Address (Imm64 4w) then (bir_mod2_post pre_x10)
        else bir_exp_false)
Proof
 cheat
QED

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_mod2_thm =
 get_riscv_contract_sing
  bir_cont_mod2
  ``bir_mod2_progbin``
  ``riscv_mod2_pre pre_x10`` ``riscv_mod2_post pre_x10`` bir_mod2_prog_def
  [bir_mod2_pre_def]
  bir_mod2_pre_def mod2_riscv_pre_imp_bir_pre_thm
  [bir_mod2_post_def] mod2_riscv_post_imp_bir_post_thm
  bir_mod2_riscv_lift_THM;

Theorem riscv_cont_mod2[local]:
 riscv_cont bir_mod2_progbin 0w {4w} (riscv_mod2_pre pre_x10) (riscv_mod2_post pre_x10)
Proof
 ACCEPT_TAC riscv_cont_mod2_thm
QED

val _ = export_theory ();
