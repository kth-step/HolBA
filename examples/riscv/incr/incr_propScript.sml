open HolKernel boolLib Parse bossLib;

open markerTheory;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

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

open bir_env_oldTheory;
open bir_program_varsTheory;

open incrTheory;
open incr_symb_execTheory;

val _ = new_theory "incr_prop";

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_incr_pre_def:
 riscv_incr_pre x (m : riscv_state) =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_incr_post_def:
 riscv_incr_post x (m : riscv_state) =
  (m.c_gpr m.procID 10w = x + 1w)
End

(* ------------ *)
(* BIR contract *)
(* ------------ *)

Definition bir_incr_pre_def:
  bir_incr_pre x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bir_incr_post_def:
 bir_incr_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (x + 1w)))
End

val bir_incr_pre = ``bir_incr_pre``;
val bir_incr_post = ``bir_incr_post``;

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem incr_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir (riscv_incr_pre pre_x10) (bir_incr_pre pre_x10)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_incr_pre_def,bir_incr_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

Theorem incr_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_incr_post pre_x10) (\l. bir_incr_post pre_x10) ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_incr_post_def,bir_incr_post_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Q.ABBREV_TAC `g = ?z. f "x10" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   fs [Abbrev_def] >>
   `bir_eval_bin_pred BIExp_Equal (SOME z)
     (SOME (BVal_Imm (Imm64 (pre_x10 + 1w)))) = SOME bir_val_true`
    by METIS_TAC [] >>   
   Cases_on `z` >> fs [type_of_bir_val_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def,bir_immTheory.bool2b_def,bir_val_true_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_def] >>
   Q.ABBREV_TAC `bb = bir_bin_pred BIExp_Equal b' (Imm64 (pre_x10 + 1w))` >>
   Cases_on `bb` >> fs [] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_Equal_REWR] >> 
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) incr_symb_analysis_thm;

Definition incr_analysis_L_def:
 incr_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 4w))``;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

(*
Definition bsysprecond_def:
  bsysprecond x = FST (THE (birs_eval_exp (^bir_incr_pre x) (bir_senv_GEN_list incr_birenvtyl)))
End

Theorem bir_incr_pre_birs_eval_exp_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC
   birs_stepLib.birs_eval_exp_CONV)
     ``birs_eval_exp (bir_incr_pre pre_x10) (bir_senv_GEN_list incr_birenvtyl)``

Theorem bsysprecond_thm =
 (REWRITE_CONV [bsysprecond_def, birs_eval_exp_ALT_thm, bir_incr_pre_birs_eval_exp_thm] THENC EVAL) ``bsysprecond pre_x10``

Theorem bir_incr_pre_birs_eval_exp_thm2 = REWRITE_CONV [bir_incr_pre_birs_eval_exp_thm, GSYM bsysprecond_thm] ``birs_eval_exp (bir_incr_pre pre_x10) (bir_senv_GEN_list incr_birenvtyl)``

val bsysprecond = (fst o dest_eq o concl o Q.SPEC `pre_x10`) bsysprecond_def;

val birs_state_init_pre = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list incr_birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := ^bsysprecond
|>``;
*)



(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)
Definition P_bircont_def:
  P_bircont envtyl bpre ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       pc.bpc_index = 0 /\ (* TODO: comment here why do we need this? *)
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





val birs_state_init_pre = ``birs_state_init_pre_GEN ^birs_state_init_lbl incr_birenvtyl (mk_bsysprecond (bir_incr_pre pre_x10) incr_birenvtyl)``;

val incr_bsysprecond_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV) ``mk_bsysprecond (bir_incr_pre pre_x10) incr_birenvtyl``;

Theorem birs_state_init_pre_EQ_thm:
  ^((snd o dest_comb) sys_i) = ^birs_state_init_pre
Proof
  REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, incr_bsysprecond_thm] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
QED

val incr_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm, GSYM bir_incr_prog_def] incr_symb_analysis_thm;

Theorem incr_birenvtyl_EVAL_thm =
 (REWRITE_CONV [incr_birenvtyl_def,
   bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
   bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL)
 ``incr_birenvtyl``;

val birs_state_thm = REWRITE_CONV [incr_birenvtyl_EVAL_thm] birs_state_init_pre;

(* ------ *)

(* now the transfer *)

val bprog_tm = (fst o dest_eq o concl) bir_incr_prog_def;

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);

Definition bprog_P_def:
  bprog_P x = P_bircont incr_birenvtyl (^bir_incr_pre x)
End

(*
(\env. bir_env_lookup "x10" env = SOME (BVal_Imm (Imm64 (x + 1w))))
*)
Definition bprog_Q_def:
  bprog_Q x = Q_bircont (^birs_state_end_lbl) (set incr_prog_vars) (^bir_incr_post x)
End

Definition pre_bir_def:
  pre_bir x bs =
       (bir_eval_exp (^bir_incr_pre x) bs.bst_environ = SOME bir_val_true)
End

Definition post_bir_def:
  post_bir x bs1 bs2 =
       (bir_eval_exp (^bir_incr_post x) bs2.bst_environ = SOME bir_val_true)
End

Definition pre_bir_nL_def:
  pre_bir_nL x st =
      (
       st.bst_status = BST_Running /\
       st.bst_pc.bpc_index = 0 /\
       bir_envty_list_b incr_birenvtyl st.bst_environ /\

       pre_bir x st
      )
End
Definition post_bir_nL_def:
  post_bir_nL x (st:bir_state_t) st' =
      (
         (st'.bst_pc = ^birs_state_end_lbl) /\
         st'.bst_status = BST_Running /\
         bir_env_vars_are_initialised st'.bst_environ (set incr_prog_vars) /\

         post_bir x st st'
      )
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
  ASSUME_TAC (GSYM incr_prog_vars_thm) >>
  `incr_prog_vars = MAP PairToBVar incr_birenvtyl` by (
    SIMP_TAC std_ss [incr_birenvtyl_def, listTheory.MAP_MAP_o, PairToBVar_BVarToPair_I_thm, listTheory.MAP_ID]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  IMP_RES_TAC (SIMP_RULE std_ss [] P_bircont_entails_thm) >>

  SIMP_TAC std_ss [bprog_P_def] >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `bir_incr_pre pre_x10`) >>
  `bir_vars_of_exp (bir_incr_pre pre_x10) SUBSET set (MAP PairToBVar incr_birenvtyl)` by (
    PAT_X_ASSUM ``A = set B`` (fn thm => REWRITE_TAC [GSYM thm]) >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_incr_pre_def, bir_incr_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def, bir_incr_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  `ALL_DISTINCT (MAP FST incr_birenvtyl)` by (
    SIMP_TAC (std_ss++listSimps.LIST_ss) [incr_birenvtyl_EVAL_thm]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  `IS_SOME (type_of_bir_exp (bir_incr_pre pre_x10))` by (
    SIMP_TAC std_ss [bir_incr_pre_def, bir_incr_pre_def] >>
    CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) type_of_bir_exp_thms)) >>
    SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES]
  ) >>
  POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm])
(*>>
  POP_ASSUM (ASSUME_TAC o SPEC birs_state_init_lbl) >>

  FULL_SIMP_TAC std_ss [mk_bsysprecond_def, GSYM bsysprecond_def] >>

  FULL_SIMP_TAC std_ss [birs_state_init_pre_GEN_def]
*)
QED




(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)
(*
val varset_thm = incr_prog_vars_thm;
*)
fun Q_bircont_SOLVE3CONJS_TAC varset_thm = (
    FULL_SIMP_TAC (std_ss) [Q_bircont_thm] >>
    (* pc *)
    CONJ_TAC >- (
      REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>
    (* status Running *)
    CONJ_TAC >- (
      REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>

    (* bir_env_vars_are_initialised *)
    CONJ_TAC >- (
      PAT_X_ASSUM ``A = B`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      PAT_X_ASSUM ``A = B`` (K ALL_TAC) >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def, varset_thm] >>

      IMP_RES_TAC birs_env_vars_are_initialised_IMP_thm >>
      POP_ASSUM (K ALL_TAC) >>
      PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ((snd o dest_eq o concl) varset_thm)) >>
      POP_ASSUM (MATCH_MP_TAC) >>

      (* cleanup proof state *)
      REPEAT (POP_ASSUM (K ALL_TAC)) >>

      (* concretize and normalize *)
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm, birs_auxTheory.birs_exps_of_senv_thm] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_gen_env_def, birs_gen_env_fun_def, birs_gen_env_fun_def, bir_envTheory.bir_env_lookup_def] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_auxTheory.birs_exps_of_senv_COMP_thm] >>
      CONV_TAC (RATOR_CONV (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_exp``] THENC SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL))) >>
      (* TODO: improve this *)
      CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_program``] THENC SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [] THENC EVAL)) >>

      (* finish the proof *)
      REWRITE_TAC [birs_env_vars_are_initialised_INSERT_thm, birs_env_vars_are_initialised_EMPTY_thm, birs_env_var_is_initialised_def] >>
      EVAL_TAC >>
      SIMP_TAC (std_ss++holBACore_ss) [] >>
      EVAL_TAC
    )
);




(* ........................... *)
(* proof for each end state individually: *)

val sys1 = birs_state_init_pre;
val (Pi_func, Pi_set) = dest_comb Pi_f;
(* Pi_func should be exactly ``IMAGE birs_symb_to_symbst`` *)
val sys2s = pred_setSyntax.strip_set Pi_set;

(* FIXME: this is implicitly proven already in bir_envTheory.bir_env_read_def *)
Theorem bir_eval_precond_lookup_pre_x10_incr_thm:
!x env.
  bir_eval_exp (bir_incr_pre x) env = SOME bir_val_true ==>
  bir_env_lookup "x10" env = SOME (BVal_Imm (Imm64 x))
Proof
 rw [bir_incr_pre_def] >>
 Cases_on `env` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_exp_def,bir_eval_bin_pred_def
 ] >>
 Q.ABBREV_TAC `g = ?z. f "x10" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   fs [Abbrev_def] >>
   Cases_on `z` >> fs [type_of_bir_val_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def,bir_immTheory.bool2b_def,bir_val_true_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_def] >>
   Q.ABBREV_TAC `bb = bir_bin_pred BIExp_Equal b (Imm64 x)` >>
   Cases_on `bb` >> fs [] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_Equal_REWR]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

(*
val sys2 = hd sys2s;
*)
val Pi_thms = List.map (fn sys2 =>
  prove(``
    sys1 = ^sys1 ==>
    sys2 = ^sys2 ==>
    birs_symb_matchstate sys1 H bs ==>
    bprog_P pre_x10 (birs_symb_to_concst bs) ==>
    symb_interpr_ext H' H ==>
    birs_symb_matchstate sys2 H' bs' ==>
    bprog_Q pre_x10 (birs_symb_to_concst bs) (birs_symb_to_concst bs')
  ``,
    REWRITE_TAC [bprog_P_def, bprog_Q_def] >>
    REPEAT STRIP_TAC >>
    Q_bircont_SOLVE3CONJS_TAC incr_prog_vars_thm >>

    (* TODO: this is still hard coded for the example *)
    (* the property (here: pre_x10 + 1) *)
    `bir_env_lookup "x10" bs'.bst_environ = SOME (BVal_Imm (Imm64 (pre_x10 + 1w)))` by (
      `BVar "sy_x10" (BType_Imm Bit64) IN symb_interpr_dom H` by (
        `symb_interpr_for_symbs (birs_symb_symbols sys1) H` by (
          FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
        ) >>

        PAT_X_ASSUM ``A = ^sys1`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
        POP_ASSUM (ASSUME_TAC o CONV_RULE (
            REWRITE_CONV [birs_state_init_pre_GEN_def, incr_bsysprecond_thm] THENC
            REWRITE_CONV [birenvtyl_EVAL_thm] THENC
            computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC
            aux_setLib.birs_symb_symbols_MATCH_CONV)
          ) >>

        FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
      ) >>
      `BVar "sy_x10" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
        `symb_interpr_for_symbs (birs_symb_symbols sys2) H'` by (
          FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
        ) >>

        PAT_X_ASSUM ``A = ^sys2`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
        POP_ASSUM (ASSUME_TAC o CONV_RULE (
            REWRITE_CONV [birs_state_init_pre_GEN_def, incr_bsysprecond_thm] THENC
            REWRITE_CONV [birenvtyl_EVAL_thm] THENC
            computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC
            aux_setLib.birs_symb_symbols_MATCH_CONV)
          ) >>

        FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
      ) >>

      `symb_interpr_get H' (BVar "sy_x10" (BType_Imm Bit64)) = symb_interpr_get H (BVar "sy_x10" (BType_Imm Bit64))` by (
        FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def]
      ) >>

      `bir_eval_exp (bir_incr_pre pre_x10) bs.bst_environ = SOME bir_val_true` by (
        PAT_X_ASSUM ``A = ^sys1`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
        FULL_SIMP_TAC (std_ss) [P_bircont_thm]
      ) >>

      (* use bprog_P, but can also use the path condition in the end, or not? *)
      `symb_interpr_get H (BVar "sy_x10" (BType_Imm Bit64)) = SOME (BVal_Imm (Imm64 pre_x10))` by (
        FULL_SIMP_TAC (std_ss) [P_bircont_thm] >>
        `bir_env_lookup "x10" bs.bst_environ = SOME (BVal_Imm (Imm64 pre_x10))` by (
          METIS_TAC [bir_eval_precond_lookup_pre_x10_incr_thm]
        ) >>


        PAT_X_ASSUM ``A = ^sys1`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
        FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

        FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def, birs_interpret_fun_thm] >>
        REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"x10"`)) >>
        FULL_SIMP_TAC (std_ss) [] >>
        REV_FULL_SIMP_TAC (std_ss) [birs_interpret_fun_ALT_def, birs_interpret_get_var_def]
      ) >>

      (* now go through H' and sys2 with matchstate to show that the increment holds in bs' *)
      PAT_X_ASSUM ``A = ^sys2`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"x10"`)) >>
      FULL_SIMP_TAC (std_ss) [] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def, birs_interpret_fun_thm] >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"x10"`)) >>
      FULL_SIMP_TAC (std_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss) [birs_interpret_fun_ALT_def, birs_interpret_get_var_def] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_incr_post_def, bir_eval_bin_pred_def, bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def] >>
    EVAL_TAC
  )
) sys2s;

(* ........................... *)

(* Q is implied by sys and Pi *)
Theorem bprog_Pi_overapprox_Q_thm[local]:
  Pi_overapprox_Q (bir_symb_rec_sbir ^bprog_tm) (bprog_P pre_x10) (birs_symb_to_symbst ^birs_state_init_pre) ^Pi_f(*(IMAGE birs_symb_to_symbst {a;b;c;d})*) (bprog_Q pre_x10)
Proof
  REWRITE_TAC [bir_prop_transferTheory.bir_Pi_overapprox_Q_thm] >>
  REPEAT GEN_TAC >>

  REWRITE_TAC [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [] >>
    METIS_TAC Pi_thms
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
    incr_analysis_thm;

(* lift to concrete state property *)
val bprog_concst_prop_thm =
  SIMP_RULE (std_ss++birs_state_ss)
    [birs_state_init_pre_GEN_def, birs_symb_symbst_pc_thm]
    (REWRITE_RULE
      [symb_prop_transferTheory.prop_holds_def]
      bprog_prop_holds_thm);
(* ........................... *)


(* lift to concrete bir property *)
Theorem bprog_to_concst_prop_thm:
  !st.
  (symb_concst_pc (birs_symb_to_concst st) = (^birs_state_init_lbl)) ==>
  (bprog_P pre_x10 (birs_symb_to_concst st)) ==>
  (?n st'.
     (step_n_in_L
       (symb_concst_pc o birs_symb_to_concst)
       (SND o bir_exec_step (^bprog_tm))
       st
       n
       (^L_s)
       st')
     /\
     (bprog_Q pre_x10 (birs_symb_to_concst st) (birs_symb_to_concst st')))
Proof
REPEAT STRIP_TAC >>
  IMP_RES_TAC (HO_MATCH_MP birs_symb_to_concst_PROP_FORALL_thm bprog_concst_prop_thm) >>

  FULL_SIMP_TAC (std_ss++symb_typesLib.symb_TYPES_ss) [conc_step_n_in_L_def, bir_symb_rec_sbir_def] >>

  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [] >>

  `birs_symb_to_concst o SND o bir_exec_step ^bprog_tm o
             birs_symb_from_concst =
   birs_symb_to_concst o (SND o bir_exec_step ^bprog_tm) o
             birs_symb_from_concst` by (
    FULL_SIMP_TAC (std_ss) []
  ) >>
  FULL_SIMP_TAC (pure_ss) [] >>

  FULL_SIMP_TAC (pure_ss) [
    SIMP_RULE std_ss [birs_symb_to_from_concst_thm, birs_symb_to_concst_EXISTS_thm, birs_symb_to_concst_EQ_thm] (
      SPECL [``birs_symb_to_concst``, ``birs_symb_from_concst``] (
        INST_TYPE [Type`:'b` |-> Type`:(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t`, Type`:'a` |-> Type`:bir_state_t`] step_n_in_L_ABS_thm)
  )] >>

  METIS_TAC []
QED

(* finish translation to pure BIR property *)
Theorem bprog_bir_prop_thm = REWRITE_RULE
    [bprog_P_def, P_bircont_thm, bprog_Q_def, Q_bircont_thm, birs_symb_concst_pc_thm, combinTheory.o_DEF, GSYM bir_programTheory.bir_exec_step_state_def, GSYM incr_analysis_L_def]
    (REWRITE_RULE
      []
      bprog_to_concst_prop_thm)

(* ........................... *)

val bir_frag_l_tm = birs_state_init_lbl;
val bir_frag_l_ml_tm = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl o EVAL) ``(^bir_frag_l_tm).bpc_label``;

val bir_frag_l_exit_tm = birs_state_end_lbl;
val bir_frag_l_exit_ml_tm = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl o EVAL) ``(^bir_frag_l_exit_tm).bpc_label``;

Theorem bir_step_n_in_L_jgmt_thm[local]:
  bir_step_n_in_L_jgmt
  ^bprog_tm
  ^bir_frag_l_tm
  incr_analysis_L
  (pre_bir_nL pre_x10)
  (post_bir_nL pre_x10)
Proof
  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  REWRITE_TAC [pre_bir_nL_def, pre_bir_def] >>
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
  ASM_SIMP_TAC (std_ss++holBACore_ss) [incr_prog_vars_thm]
QED


Theorem incr_analysis_L_INTER_thm[local]:
  incr_analysis_L INTER
        {<|bpc_label := BL_Address (Imm64 4w); bpc_index := 0|>} =
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

Theorem bir_abstract_jgmt_rel_incr_thm[local]:
  abstract_jgmt_rel
  (bir_ts ^bprog_tm)
  (BL_Address (Imm64 ^bir_frag_l_ml_tm))
  {BL_Address (Imm64 ^bir_frag_l_exit_ml_tm)}
  (pre_bir_nL pre_x10)
  (post_bir_nL pre_x10)
Proof
ASSUME_TAC
    (Q.SPEC `{BL_Address (Imm64 ^bir_frag_l_exit_ml_tm)}`
      (MATCH_MP
        (REWRITE_RULE
           [bir_programTheory.bir_block_pc_def]
           bir_program_transfTheory.bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm)
        bir_step_n_in_L_jgmt_thm)) >>

  FULL_SIMP_TAC std_ss [pre_bir_nL_def] >>

  FULL_SIMP_TAC std_ss [IMAGE_SING, IN_SING, bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [incr_analysis_L_INTER_thm] >>

  FULL_SIMP_TAC std_ss [post_bir_nL_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [abstract_jgmt_rel_def]
QED


Theorem bir_state_restrict_vars_envty_list_b_spec_thm:
  !vs st st'.
    (vs = bir_vars_of_program ^bprog_tm) ==>
    (st' = bir_state_restrict_vars vs st) ==>
    (bir_env_vars_are_initialised st.bst_environ vs) ==>
    (bir_envty_list_b incr_birenvtyl st'.bst_environ)
Proof
  `ALL_DISTINCT (MAP FST incr_birenvtyl)` by (
    SIMP_TAC (std_ss++listSimps.LIST_ss) [incr_birenvtyl_EVAL_thm]
  ) >>
  REPEAT STRIP_TAC >>
  `set (MAP PairToBVar incr_birenvtyl) = vs` by (
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [GSYM incr_prog_vars_thm, incr_birenvtyl_def, listTheory.MAP_MAP_o, birs_auxTheory.PairToBVar_BVarToPair_I_thm]
  ) >>
  METIS_TAC [bir_state_restrict_vars_envty_list_b_thm]
QED

Theorem bir_incr_pre_EQ_FOR_VARS_thm:
  !vs st1 st2 x.
    (vs = bir_vars_of_program ^bprog_tm) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_eval_exp (bir_incr_pre x) st1.bst_environ = SOME bir_val_true) ==>
    (bir_eval_exp (bir_incr_pre x) st2.bst_environ = SOME bir_val_true)
Proof
  REPEAT STRIP_TAC >>
  `bir_vars_of_exp (bir_incr_pre x) SUBSET vs` by (
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def, bir_incr_pre_def] >>
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>
  METIS_TAC [bir_envTheory.bir_env_EQ_FOR_VARS_SUBSET, bir_vars_of_exp_THM_EQ_FOR_VARS, bir_state_EQ_FOR_VARS_ALT_DEF]
QED
Theorem bir_incr_post_EQ_FOR_VARS_thm:
  !vs st1 st2 x.
    (vs = bir_vars_of_program ^bprog_tm) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_eval_exp (bir_incr_post x) st1.bst_environ = SOME bir_val_true) ==>
    (bir_eval_exp (bir_incr_post x) st2.bst_environ = SOME bir_val_true)
Proof
  REPEAT STRIP_TAC >>
  `bir_vars_of_exp (bir_incr_post x) SUBSET vs` by (
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def, bir_incr_post_def] >>
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>
  METIS_TAC [bir_envTheory.bir_env_EQ_FOR_VARS_SUBSET, bir_vars_of_exp_THM_EQ_FOR_VARS, bir_state_EQ_FOR_VARS_ALT_DEF]
QED

Theorem pre_bir_nL_vars_EQ_precond_IMP_thm:
  !vs st1 st2.
    (vs = bir_vars_of_program ^bprog_tm) ==>
    (st2 = bir_state_restrict_vars vs st1) ==>
    (bir_exec_to_labels_triple_precond st1 (bir_incr_pre pre_x10) ^bprog_tm) ==>
    (pre_bir_nL pre_x10 st2)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  STRIP_TAC >>

  `bir_envty_list_b incr_birenvtyl st2.bst_environ` by (
    METIS_TAC [bir_state_restrict_vars_envty_list_b_spec_thm, bir_exec_to_labels_triple_precond_def] (* for the reduced state st2, we can prove this *)
  ) >>
  (* we get this from the restriction, the rest must be due to the equality for the variables *)
  `bir_state_EQ_FOR_VARS vs st1 st2` by (
    METIS_TAC [bir_vars_EQ_state_restrict_vars_THM]
  ) >>

  FULL_SIMP_TAC std_ss [pre_bir_nL_def, pre_bir_def, bir_exec_to_labels_triple_precond_def] >>
  METIS_TAC [bir_incr_pre_EQ_FOR_VARS_thm, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
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

Theorem post_bir_nL_vars_EQ_postcond_IMP_thm:
  !vs st1' st2' st2.
    (vs = bir_vars_of_program ^bprog_tm) ==>
    (bir_state_EQ_FOR_VARS vs st1' st2') ==>
    (post_bir_nL pre_x10 st2 st2') ==>
    (bir_exec_to_labels_triple_postcond st1' (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false) ^bprog_tm)
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [post_bir_nL_def, bir_exec_to_labels_triple_postcond_def] >>

  `bir_env_vars_are_initialised st1'.bst_environ vs` by (
    METIS_TAC [bir_state_EQ_FOR_VARS_env_vars_are_initialised_thm, bir_state_EQ_FOR_VARS_SYM_thm, incr_prog_vars_thm]
  ) >>
  `st1'.bst_pc.bpc_label = BL_Address (Imm64 4w) /\ st1'.bst_pc.bpc_index = 0` by (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
  ) >>
  `bir_is_bool_exp_env st1'.bst_environ (bir_incr_post pre_x10)` by (
    `bir_env_var_is_initialised st1'.bst_environ (BVar "x10" (BType_Imm Bit64))` by (
      PAT_X_ASSUM ``bir_vars_of_program A = B`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss) [] >>

      FULL_SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def] >>
      FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY]
    ) >>
    REWRITE_TAC [bir_incr_post_def] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, EVAL ``bool2b T``, bir_val_true_def] >>

    REWRITE_TAC [bir_bool_expTheory.bir_is_bool_exp_env_REWRS, bir_typing_expTheory.bir_vars_of_exp_def] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

    FULL_SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def] >>

    FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY]
  ) >>
  ASM_SIMP_TAC std_ss [] >>

  METIS_TAC [bir_incr_post_EQ_FOR_VARS_thm, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_EQ_FOR_VARS_SYM_thm, post_bir_def]
QED

Theorem abstract_jgmt_rel_incr[local]:
 abstract_jgmt_rel (bir_ts ^bprog_tm) (BL_Address (Imm64 0w)) {BL_Address (Imm64 4w)}
  (\st. bir_exec_to_labels_triple_precond st (bir_incr_pre pre_x10) ^bprog_tm)
  (\st st'. bir_exec_to_labels_triple_postcond st' (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false) ^bprog_tm)
Proof
  ASSUME_TAC bir_abstract_jgmt_rel_incr_thm >>

  FULL_SIMP_TAC std_ss [abstract_jgmt_rel_def] >>

  REPEAT STRIP_TAC >>

  (* reduce st here to a state that only has the program variables and is equal in all program variables, st_r, then use this new state instead in the next line *)
  Q.ABBREV_TAC `vs = bir_vars_of_program (bir_incr_prog:'observation_type bir_program_t)` >>
  Q.ABBREV_TAC `st_r = bir_state_restrict_vars vs st` >>
  `bir_state_EQ_FOR_VARS vs st st_r` by (
    METIS_TAC [bir_vars_EQ_state_restrict_vars_THM]
  ) >>
  (* here we prove that all the precondition stuff also holds in st_r *)
  `pre_bir_nL pre_x10 st_r /\ (bir_ts (bir_incr_prog:'observation_type bir_program_t)).ctrl st_r = BL_Address (Imm64 0w)` by (
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_ts_def] >>
    METIS_TAC [pre_bir_nL_vars_EQ_precond_IMP_thm, bir_program_varsTheory.bir_state_EQ_FOR_VARS_ALT_DEF]
  ) >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPECL [`st_r`]) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>

  (* because st_r equals st in the program variables, we know that the weak transition from st and st_r leads to a state that is equal in the program variables *)
  `?st'. (bir_ts (bir_incr_prog:'observation_type bir_program_t)).weak {BL_Address (Imm64 4w)} st st' /\ bir_state_EQ_FOR_VARS vs ms' st'` by (
    METIS_TAC [bir_prop_transferTheory.bir_vars_bir_ts_thm, bir_state_EQ_FOR_VARS_SYM_thm]
  ) >>
  Q.EXISTS_TAC `st'` >>
  REV_FULL_SIMP_TAC (std_ss) [] >>

  (* TODO: and because these are equal the postcondition stuff is established as well *)
  METIS_TAC [post_bir_nL_vars_EQ_postcond_IMP_thm, bir_state_EQ_FOR_VARS_SYM_thm]
QED

Theorem bir_cont_incr_tm[local]:
 bir_cont ^bprog_tm bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_incr_pre pre_x10)
  (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false)
Proof
 `{BL_Address (Imm64 4w)} <> {}` by fs [] >>
 MP_TAC ((Q.SPECL [
  `BL_Address (Imm64 0w)`,
  `{BL_Address (Imm64 4w)}`,
  `bir_incr_pre pre_x10`,
  `\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false`
 ] o SPEC bprog_tm o INST_TYPE [Type.alpha |-> Type`:'observation_type`]) abstract_jgmt_rel_bir_cont) >>
 rw [] >>
 METIS_TAC [abstract_jgmt_rel_incr]
QED

Theorem bir_cont_incr:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_incr_pre pre_x10)
   (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10)
        else bir_exp_false)
Proof
 rw [bir_incr_prog_def,bir_cont_incr_tm]
QED

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_incr_thm =
 get_riscv_contract_sing
  bir_cont_incr
  ``bir_incr_progbin``
  ``riscv_incr_pre pre_x10`` ``riscv_incr_post pre_x10`` bir_incr_prog_def
  [bir_incr_pre_def]
  bir_incr_pre_def incr_riscv_pre_imp_bir_pre_thm
  [bir_incr_post_def] incr_riscv_post_imp_bir_post_thm
  bir_incr_riscv_lift_THM;

Theorem riscv_cont_incr:
 riscv_cont bir_incr_progbin 0w {4w} (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)
Proof
 ACCEPT_TAC riscv_cont_incr_thm
QED

val _ = export_theory ();
