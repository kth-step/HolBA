structure bir_symbLib :> bir_symbLib =
struct

open Abbrev;

local
  open HolKernel Parse boolLib bossLib;
  open bitTheory;
  open birs_stepLib;
  open birs_composeLib;
  open birs_driveLib;
  open birs_auxTheory;
in

val prog_addr_max_tm = ``0x20000w:word64``;

val mem_addr_bound_tm = ``0x100000000w:word64``;

fun mem_addrs_stack_disj_reg_bir_tm rnsp rn = ``BExp_BinPred BIExp_LessThan
     (BExp_Den (BVar ^(stringSyntax.fromMLstring rnsp) (BType_Imm Bit64)))
     (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))``;
(*
fun mem_area_disj_reg_bir_tm rn1 sz1 rn2 sz2 = ``BExp_BinExp BIExp_And
 (BExp_BinPred BIExp_LessOrEqual
  (BExp_Const (Imm64 ^prog_addr_max_tm))
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64))))
 (BExp_BinPred BIExp_LessThan
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
  (BExp_Const (Imm64 ^mem_addr_bound_tm)))``;
*)

fun mem_addrs_prog_disj_bir_tm rn = ``BExp_BinExp BIExp_And
 (BExp_BinPred BIExp_LessOrEqual
  (BExp_Const (Imm64 ^prog_addr_max_tm))
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64))))
 (BExp_BinPred BIExp_LessThan
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
  (BExp_Const (Imm64 ^mem_addr_bound_tm)))``;

fun mem_addrs_aligned_prog_disj_bir_tm rn = ``BExp_BinExp BIExp_And
  (BExp_Aligned Bit64 3 (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64))))
  (^(mem_addrs_prog_disj_bir_tm rn))``;

fun mem_addrs_aligned_prog_disj_riscv_tm vn =
 let
   val var_tm = mk_var (vn, wordsSyntax.mk_int_word_type 64)
 in
  ``^var_tm && 7w = 0w /\ ^prog_addr_max_tm <=+ ^var_tm /\ ^var_tm <+ ^mem_addr_bound_tm``
 end;

fun pre_vals_reg_bir_tm rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
      (BExp_Const (Imm64 `@ [QUOTE fv] @`)))
`);

fun pre_vals_mem_reg_bir_tm mn rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Load
        (BExp_Den (BVar ^(stringSyntax.fromMLstring mn) (BType_Mem Bit64 Bit8)))
        (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
        BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 `@ [QUOTE fv] @`)))
`);

fun pre_vals_bir_tm mn rn fvr fvmd =
 bslSyntax.band (pre_vals_reg_bir_tm rn fvr, pre_vals_mem_reg_bir_tm mn rn fvmd);

fun bir_symb_analysis bprog_tm birs_state_init_lbl
  birs_end_lbls bprog_envtyl birs_pcond =
 let
   val birs_state_init = ``<|
     bsst_pc       := ^birs_state_init_lbl;
     bsst_environ  := bir_senv_GEN_list ^bprog_envtyl;
     bsst_status   := BST_Running;
     bsst_pcond    := ^birs_pcond
   |>``;
   val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
   val birs_rule_STEP_fun_spec =
     (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o
      birs_rule_tryjustassert_fun true o birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm);
   (* now the composition *)
   val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
   val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
   val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
   (* and also the sequential composition *)
   val birs_rule_STEP_SEQ_thm = MATCH_MP
    birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm
    (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_STEP_SEQ_fun_spec =
    birs_rule_STEP_SEQ_fun (birs_rule_SUBST_thm, birs_rule_STEP_SEQ_thm);
   val _ = print "now reducing it to one sound structure\n";
   val timer = bir_miscLib.timer_start 0;
   val result = exec_until
     (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec)
     single_step_A_thm birs_end_lbls;
   val _ = bir_miscLib.timer_stop
    (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;
 in
   result
 end (* let *)

fun bir_symb_analysis_thm bir_prog_def
 init_addr_def end_addr_defs bspec_pre_def birenvtyl_def =
 let
   val bprog_tm = (snd o dest_eq o concl) bir_prog_def;
   val init_addr_tm = (snd o dest_eq o concl) init_addr_def;
   val birs_state_init_lbl_tm =
    (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
   val birs_state_end_tm_lbls =
    List.map 
     (fn end_addr_def =>
       let val end_addr_tm = (snd o dest_eq o concl) end_addr_def in
         (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))`` 
       end) end_addr_defs;
   val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_pre_def;
   val bprog_envtyl_tm = (fst o dest_eq o concl) birenvtyl_def;

   val bsysprecond_thm =
     (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
       ``mk_bsysprecond ^bspec_pre_tm ^bprog_envtyl_tm``;
   val birs_pcond_tm = (snd o dest_eq o concl) bsysprecond_thm;

   val symb_analysis_thm = bir_symb_analysis
    bprog_tm birs_state_init_lbl_tm birs_state_end_tm_lbls
    bprog_envtyl_tm birs_pcond_tm;
 in
   (bsysprecond_thm, symb_analysis_thm)
 end (* let *)

end (* local *)

local
  open HolKernel boolLib Parse bossLib;
  open markerTheory;
  open distribute_generic_stuffLib;
  open bir_programSyntax bir_program_labelsTheory;
  open bir_immTheory bir_valuesTheory bir_expTheory;
  open bir_tsTheory bir_bool_expTheory bir_programTheory;
  open bir_compositionLib;
  open bir_lifting_machinesTheory;
  open bir_typing_expTheory;
  open bir_htTheory;
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
  open distribute_generic_stuffTheory;
in

fun bir_symb_transfer init_addr_tm end_addr_tm bspec_pre_tm bspec_post_tm
 bir_prog_def birenvtyl_def bspec_pre_def bspec_post_def prog_vars_def
 symb_analysis_thm bsysprecond_thm prog_vars_thm =
 let 
   val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
   val bprog_tm = (fst o dest_eq o concl) bir_prog_def;
   val prog_vars_tm = (fst o dest_eq o concl) prog_vars_def;
   val birenvtyl_tm = (fst o dest_eq o concl) birenvtyl_def;
   val bir_state_init_lbl_tm = (snd o dest_eq o concl o EVAL)
    ``bir_block_pc (BL_Address (Imm64 ^init_addr_tm))``;
   val birs_state_end_lbl_tm = (snd o dest_eq o concl o EVAL)
    ``bir_block_pc (BL_Address (Imm64 ^end_addr_tm))``;
   val birs_state_init_pre_tm =
    ``birs_state_init_pre_GEN ^bir_state_init_lbl_tm ^birenvtyl_tm
      (mk_bsysprecond ^bspec_pre_tm ^birenvtyl_tm)``;

   val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) symb_analysis_thm;

   val analysis_L_NOTIN_thm = prove (``^birs_state_end_lbl_tm NOTIN ^L_s``, EVAL_TAC);

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
    `^prog_vars_tm = MAP PairToBVar ^birenvtyl_tm` by (
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

   val strongpostcond_goals = List.map (fn sys2 => ``
    sys1 = ^sys1 ==>
    sys2 = ^sys2 ==>
    birs_symb_matchstate sys1 H' bs ==>
    bir_eval_exp ^bspec_pre_tm bs.bst_environ = SOME bir_val_true ==>
    birs_symb_matchstate sys2 H' bs' ==>
    bir_eval_exp ^bspec_post_tm bs'.bst_environ = SOME bir_val_true``) 
   sys2s;

   val strongpostcond_thms = List.map (fn goal =>
    prove(``^goal``, birs_strongpostcond_impl_TAC)) strongpostcond_goals;

   val Pi_thms = List.map (fn sys2 =>
    prove(``
     sys1 = ^sys1 ==>
     sys2 = ^sys2 ==>
     birs_symb_matchstate sys1 H bs ==>
     P_bircont ^birenvtyl_tm ^bspec_pre_tm (birs_symb_to_concst bs) ==>
     symb_interpr_ext H' H ==>
     birs_symb_matchstate sys2 H' bs' ==>
     Q_bircont ^birs_state_end_lbl_tm (set ^prog_vars_tm) ^bspec_post_tm
      (birs_symb_to_concst bs) (birs_symb_to_concst bs')``,

    REPEAT STRIP_TAC >>
    Q_bircont_SOLVE3CONJS_TAC prog_vars_thm >>
    `birs_symb_matchstate sys1 H' bs` by
     METIS_TAC [bir_symb_soundTheory.birs_symb_matchstate_interpr_ext_IMP_matchstate_thm] >>
    FULL_SIMP_TAC std_ss [P_bircont_thm] >>
    METIS_TAC strongpostcond_thms))
   sys2s;

   val bprog_Pi_overapprox_Q_thm =
    prove (``Pi_overapprox_Q
     (bir_symb_rec_sbir ^bprog_tm)
     (P_bircont ^birenvtyl_tm ^bspec_pre_tm)
     (birs_symb_to_symbst ^birs_state_init_pre_tm) ^Pi_f
     (Q_bircont ^birs_state_end_lbl_tm (set ^prog_vars_tm) ^bspec_post_tm)``,

    REWRITE_TAC [bir_prop_transferTheory.bir_Pi_overapprox_Q_thm, bsysprecond_thm] >>
    REPEAT GEN_TAC >>
    REWRITE_TAC [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
    REPEAT STRIP_TAC >> (
     FULL_SIMP_TAC std_ss [] >>
     METIS_TAC Pi_thms));

   val bprog_prop_holds_thm =
     SIMP_RULE (std_ss++birs_state_ss)
      [birs_state_init_pre_GEN_def, birs_symb_symbst_pc_thm] (
        MATCH_MP
        (MATCH_MP
         (MATCH_MP
          birs_prop_transfer_thm
          bprog_P_entails_thm)
         bprog_Pi_overapprox_Q_thm)
        analysis_thm);

   val bir_abstract_jgmt_rel_thm =
    (MATCH_MP
     (MATCH_MP prop_holds_TO_abstract_jgmt_rel_thm analysis_L_NOTIN_thm)
     (REWRITE_RULE [] bprog_prop_holds_thm));

   val abstract_jgmt_rel_thm =
    prove (``abstract_jgmt_rel (bir_ts ^bprog_tm)
     (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)}
     (\st. bir_exec_to_labels_triple_precond st ^bspec_pre_tm ^bprog_tm)
     (\st st'. bir_exec_to_labels_triple_postcond st'
     (\l. if l = BL_Address (Imm64 ^end_addr_tm)
          then ^bspec_post_tm
          else bir_exp_false) ^bprog_tm)``,

    MATCH_MP_TAC (REWRITE_RULE
     [boolTheory.AND_IMP_INTRO] abstract_jgmt_rel_bir_exec_to_labels_triple_thm) >>
    SIMP_TAC std_ss [] >>
    EXISTS_TAC birenvtyl_tm >>
    CONJ_TAC >- (
     (* bpre subset *)
     REWRITE_TAC [bspec_pre_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT] >>
     EVAL_TAC
    ) >>
    CONJ_TAC >- (
     (* bpost subset *)
     REWRITE_TAC [bspec_post_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
    ) >>
    CONJ_TAC >- (
     (* bpost is bool *)
     REWRITE_TAC [bspec_post_def] >>
     SIMP_TAC (std_ss++holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def]
    ) >>
    CONJ_TAC >- (
     (* ALL_DISTINCT envtyl *)
     SIMP_TAC (std_ss++listSimps.LIST_ss) [birenvtyl_EVAL_thm] >>
     EVAL_TAC
    ) >>
    CONJ_TAC >- (
     (* envtyl = vars_of_prog *)
     REWRITE_TAC [GSYM prog_vars_thm] >>
     SIMP_TAC std_ss [birenvtyl_def, listTheory.MAP_MAP_o, PairToBVar_BVarToPair_I_thm, listTheory.MAP_ID]
    ) >>
    METIS_TAC [bir_abstract_jgmt_rel_thm, prog_vars_thm]);

  val bspec_cont_thm =
   prove (``bir_cont ^bprog_tm bir_exp_true
    (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_tm)} {}
    ^bspec_pre_tm
    (\l. if l = BL_Address (Imm64 ^end_addr_tm)
         then ^bspec_post_tm
         else bir_exp_false)``,

    `{BL_Address (Imm64 ^end_addr_tm)} <> {}` by fs [] >>
    MP_TAC ((Q.SPECL [
     `BL_Address (Imm64 ^init_addr_tm)`,
      `{BL_Address (Imm64 ^end_addr_tm)}`,
      `^bspec_pre_tm`,
      `\l. if l = BL_Address (Imm64 ^end_addr_tm)
           then ^bspec_post_tm
           else bir_exp_false`
    ] o SPEC bprog_tm o INST_TYPE [Type.alpha |-> Type`:'observation_type`])
    abstract_jgmt_rel_bir_cont) >>
    rw [] >>
    METIS_TAC [abstract_jgmt_rel_thm]);
 in
   bspec_cont_thm
 end (* let *)

end (* local *)

end (* structure *)
