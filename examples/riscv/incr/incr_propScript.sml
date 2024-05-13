open HolKernel boolLib Parse bossLib;

open markerTheory;

open distribute_generic_stuffLib;

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

open distribute_generic_stuffTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

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

Theorem incr_analysis_L_NOTIN_thm[local]:
  (^birs_state_end_lbl) NOTIN incr_analysis_L
Proof
  EVAL_TAC
QED

(* ........................... *)
(* ........................... *)
(* ........................... *)

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

Definition bprog_Q_def:
  bprog_Q x = Q_bircont (^birs_state_end_lbl) (set incr_prog_vars) (^bir_incr_post x)
End

Definition pre_bir_nL_def:
  pre_bir_nL x = pre_bircont_nL incr_birenvtyl (^bir_incr_pre x)
End

Definition post_bir_nL_def:
  post_bir_nL x = post_bircont_nL (^birs_state_end_lbl) (set incr_prog_vars) (^bir_incr_post x)
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
QED

(* ........................... *)
(* ........................... *)
(* ........................... *)

(* ........................... *)
(* proof for each end state individually: *)

val sys1 = birs_state_init_pre;
val (Pi_func, Pi_set) = dest_comb Pi_f;
(* Pi_func should be exactly ``IMAGE birs_symb_to_symbst`` *)
val sys2s = pred_setSyntax.strip_set Pi_set;

val strongpostcond_goals = List.map (fn sys2 => ``
    sys1 = ^sys1 ==>
    sys2 = ^sys2 ==>
    birs_symb_matchstate sys1 H' bs ==>
    bir_eval_exp (^bir_incr_pre pre_x10) bs.bst_environ = SOME bir_val_true ==>
    birs_symb_matchstate sys2 H' bs' ==>
    bir_eval_exp (^bir_incr_post pre_x10) bs'.bst_environ = SOME bir_val_true
  ``) sys2s;

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
val goal = hd strongpostcond_goals;
*)
val strongpostcond_thms = List.map (fn goal =>
  prove(``^goal``,
    REPEAT STRIP_TAC >>
    (* symbsof sys1 and sys2 IN symb_interpr_dom H' *)
    `(birs_symb_symbols sys1 UNION birs_symb_symbols sys2) SUBSET symb_interpr_dom H'` by (
      FULL_SIMP_TAC (std_ss) [UNION_SUBSET, birs_symb_matchstate_def, symb_interpr_for_symbs_def]
    ) >>
    FULL_SIMP_TAC (std_ss) [UNION_SUBSET] >>

    (* get stuff out of bpre, then through matchstate *)
    (* get stuff out of sys1 (environment and pcond) *)
    (* get all of this through matchstate with sys2 to bs' *)
    (* also get from sys2 through matchstate *)

(*
matchstate ==> know about concrete state from symbolic state info (pcond holds, symbolic values for state variables)
matchstate of post state can use same interpretation
precondition bprog also holds in bs
*)

    (* TODO: the following is still hard coded for the example *)

    (* BVar "sy_x10" (BType_Imm Bit64) IN symbsof sys1 *)
    `BVar "sy_x10" (BType_Imm Bit64) IN birs_symb_symbols sys1` by (
      ASM_REWRITE_TAC [] >>
      CONV_TAC (
          REWRITE_CONV [birs_state_init_pre_GEN_def, incr_bsysprecond_thm] THENC
          REWRITE_CONV [birenvtyl_EVAL_thm] THENC
          computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC
          aux_setLib.birs_symb_symbols_MATCH_CONV THENC
          EVAL
        )
    ) >>
    (* the property (here: pre_x10 + 1) *)
    `bir_env_lookup "x10" bs'.bst_environ = SOME (BVal_Imm (Imm64 (pre_x10 + 1w)))` by (
      `BVar "sy_x10" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
        METIS_TAC [SUBSET_DEF]
      ) >>

      (* use bprog_P, but can also use the path condition in the end *)
      `symb_interpr_get H' (BVar "sy_x10" (BType_Imm Bit64)) = SOME (BVal_Imm (Imm64 pre_x10))` by (
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

      (* now go through sys2 with matchstate to show that the increment holds in bs' *)
      PAT_X_ASSUM ``A = (B:birs_state_t)`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
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
) strongpostcond_goals;

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

    `birs_symb_matchstate sys1 H' bs` by (
      METIS_TAC [bir_symb_soundTheory.birs_symb_matchstate_interpr_ext_IMP_matchstate_thm]
    ) >>
    FULL_SIMP_TAC std_ss [P_bircont_thm] >>
    METIS_TAC strongpostcond_thms
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
  SIMP_RULE (std_ss++birs_state_ss)
    [birs_state_init_pre_GEN_def, birs_symb_symbst_pc_thm, GSYM incr_analysis_L_def] (
  MATCH_MP
    (MATCH_MP
      (MATCH_MP
         birs_prop_transfer_thm
         bprog_P_entails_thm)
      bprog_Pi_overapprox_Q_thm)
    incr_analysis_thm);

(* ........................... *)
(* ........................... *)
(* ........................... *)

Theorem bir_abstract_jgmt_rel_incr_thm[local] =
  REWRITE_RULE [GSYM post_bir_nL_def, GSYM pre_bir_nL_def]
    (MATCH_MP
      (MATCH_MP prop_holds_TO_abstract_jgmt_rel_thm incr_analysis_L_NOTIN_thm)
      (REWRITE_RULE [bprog_P_def, bprog_Q_def] bprog_prop_holds_thm));

(* ........................... *)
(* now manage the pre and postconditions into contract friendly "bir_exec_to_labels_triple_precond/postcond", need to change precondition to "bir_env_vars_are_initialised" for set of program variables *)


(* ........................... *)
(* ........................... *)
(* ........................... *)


Theorem abstract_jgmt_rel_incr[local]:
 abstract_jgmt_rel (bir_ts ^bprog_tm) (BL_Address (Imm64 0w)) {BL_Address (Imm64 4w)}
  (\st. bir_exec_to_labels_triple_precond st (bir_incr_pre pre_x10) ^bprog_tm)
  (\st st'. bir_exec_to_labels_triple_postcond st' (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10) else bir_exp_false) ^bprog_tm)
Proof
  MATCH_MP_TAC (REWRITE_RULE [boolTheory.AND_IMP_INTRO] abstract_jgmt_rel_bir_exec_to_labels_triple_thm) >>
  SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `incr_birenvtyl` >>

  CONJ_TAC >- (
    (* bpre subset *)
    REWRITE_TAC [bir_incr_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>

  CONJ_TAC >- (
    (* bpost subset *)
    REWRITE_TAC [bir_incr_post_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM incr_prog_vars_thm, incr_prog_vars_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
  ) >>

  CONJ_TAC >- (
    (* bpost is bool *)
    REWRITE_TAC [bir_incr_post_def] >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def]
  ) >>

  CONJ_TAC >- (
    (* ALL_DISTINCT envtyl *)
    SIMP_TAC (std_ss++listSimps.LIST_ss) [incr_birenvtyl_EVAL_thm]
  ) >>

  CONJ_TAC >- (
    (* envtyl = vars_of_prog *)
    REWRITE_TAC [GSYM incr_prog_vars_thm] >>
    SIMP_TAC std_ss [incr_birenvtyl_def, listTheory.MAP_MAP_o, PairToBVar_BVarToPair_I_thm, listTheory.MAP_ID]
  ) >>

  METIS_TAC [bir_abstract_jgmt_rel_incr_thm, pre_bir_nL_def, post_bir_nL_def, incr_prog_vars_thm]
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

(* unfolded theorem *)
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
val tm = concl riscv_cont_incr;
val sset = std_ss++bir_wm_SS++bir_lifting_machinesLib.bmr_ss;
val thms = [riscv_cont_def, t_jgmt_def, riscv_ts_def, riscv_weak_trs_def, riscv_incr_pre_def, riscv_incr_post_def, riscv_bmr_def, riscv_state_is_OK_def];
(*
EVAL tm;
SIMP_CONV sset thms tm
REWRITE_CONV  tm;
*)
val readable_thm = computeLib.RESTR_EVAL_CONV [``riscv_weak_trs``] tm;
Theorem riscv_incr:
  !pre_x10. ^((snd o dest_eq o concl) readable_thm)
Proof
  METIS_TAC [riscv_cont_incr, readable_thm]
QED

val _ = export_theory ();
