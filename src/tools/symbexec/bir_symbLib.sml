structure bir_symbLib :> bir_symbLib =
struct

open Abbrev;

(* error handling *)
val libname = "bir_symbLib"
val ERR = Feedback.mk_HOL_ERR libname
val wrap_exn = Feedback.wrap_exn libname

local
  open HolKernel Parse boolLib bossLib;
  open bitTheory;
  open birs_auxTheory;
  open bir_immSyntax;
in

fun bir_symb_analysis_thm bir_prog_def
 init_addr_def end_addr_defs
 bspec_pre_def birenvtyl_def =
 let
   val _ = print "\n======\n > bir_symb_analysis_thm started\n";
   val timer = holba_miscLib.timer_start 0;

   val bprog_tm = (fst o dest_eq o concl) bir_prog_def;
   val init_addr_tm = (snd o dest_eq o concl) init_addr_def;
   val init_lbl =
    (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address ^(gen_mk_Imm init_addr_tm))``;
   val birs_state_end_tm_lbls =
    List.map 
     (fn end_addr_def =>
       let val end_addr_tm = (snd o dest_eq o concl) end_addr_def in
         (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address ^(gen_mk_Imm end_addr_tm))`` 
       end) end_addr_defs;
   val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_pre_def;

   val birs_state_init =
     birs_driveLib.birs_analysis_init birenvtyl_def bspec_pre_tm init_lbl;

   val symb_analysis_thm =
     birs_driveLib.birs_exec_to
       bprog_tm
       (birs_strategiesLib.birs_post_step_riscv_default)
       (birs_strategiesLib.birs_from_summaries_riscv [])
       (birs_strategiesLib.not_at_lbls birs_state_end_tm_lbls)
       birs_state_init;

   val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n======\n > bir_symb_analysis_thm took " ^ delta_s ^ "\n")) timer;
 in
   symb_analysis_thm
 end (* let *)

end (* local *)

local
  open HolKernel boolLib Parse bossLib;
  open markerTheory;
  open distribute_generic_stuffLib;
  open bir_programSyntax bir_program_labelsTheory;
  open bir_immTheory bir_valuesTheory bir_expTheory;
  open bir_tsTheory bir_bool_expTheory bir_programTheory;
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
  open birsSyntax;
  open bir_symb_sound_coreTheory;
  open symb_recordTheory;
  open symb_interpretTheory;
  open pred_setTheory;
  open program_logicSimps;
  open bir_env_oldTheory;
  open bir_program_varsTheory;
  open distribute_generic_stuffTheory;
  open bir_immSyntax;
in

fun bir_symb_transfer
 init_addr_tm end_addr_tm
 bspec_pre_tm bspec_post_tm
 bir_prog_def birenvtyl_def
 bspec_pre_def bspec_post_def prog_vars_list_def
 symb_analysis_thm pcond_gen_inst_o prog_vars_thm =
 let
   val pcond_gen_inst =
     case pcond_gen_inst_o of
         SOME x => x
       | NONE => ``BExp_Const (Imm1 1w)``;
   val (bsysprecond_thm, symb_analysis_thm) =
     birs_transferLib.prepare_transfer
       birenvtyl_def
       pcond_gen_inst
       ((lhs o snd o strip_forall o concl) bspec_pre_def)
       symb_analysis_thm;

   val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
   val bprog_tm = (fst o dest_eq o concl) bir_prog_def;
   val prog_vars_list_tm = (fst o dest_eq o concl) prog_vars_list_def;
   val birenvtyl_tm = (fst o dest_eq o concl) birenvtyl_def;
   val bir_init_lbl_tm = ``BL_Address ^(gen_mk_Imm init_addr_tm)``;
   val bir_end_lbl_tm = ``BL_Address ^(gen_mk_Imm end_addr_tm)``;
   val bir_state_init_lbl_tm = (snd o dest_eq o concl o EVAL)
    ``bir_block_pc (BL_Address ^(gen_mk_Imm init_addr_tm))``;
   val birs_state_end_lbl_tm = (snd o dest_eq o concl o EVAL)
    ``bir_block_pc (BL_Address ^(gen_mk_Imm end_addr_tm))``;
   val birs_state_init_pre_tm =
    ``birs_state_init_pre_GEN ^bir_state_init_lbl_tm ^birenvtyl_tm
      (mk_bsysprecond ^bspec_pre_tm ^birenvtyl_tm)``;

   val (sys_i, L_s, Pi_f) = (get_birs_sysLPi o concl) symb_analysis_thm;

   val analysis_L_NOTIN_thm = prove (``^birs_state_end_lbl_tm NOTIN ^L_s``,
     REWRITE_TAC [birs_auxTheory.bir_pc_set_lbls_IN_thm] >> EVAL_TAC);

   val birs_state_init_pre_EQ_thm =
    prove (``^(sys_i) = ^birs_state_init_pre_tm``,
     REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, bsysprecond_thm] >>
     CONV_TAC (
       computeLib.RESTR_EVAL_CONV [birs_eval_exp_tm] THENC
       REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm] THENC
       birs_auxLib.GEN_match_conv is_birs_eval_exp birs_stepLib.birs_eval_exp_CONV THENC
       EVAL));

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
      CONV_TAC (RAND_CONV (bir_exp_typecheckLib.type_of_bir_exp_gen_CONV)) >>
      SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES]
    ) >>
    POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]));

   val sys1 = (snd o dest_eq o concl o REWRITE_CONV [bsysprecond_thm]) birs_state_init_pre_tm;
   val sys2s = pred_setSyntax.strip_set Pi_f;

   val strongpostcond_goals = List.map (fn sys2 => ``
    sys1 = ^sys1 ==>
    sys2 = ^sys2 ==>
    birs_symb_matchstate sys1 H' bs ==>
    bir_eval_exp ^bspec_pre_tm bs.bst_environ = SOME bir_val_true ==>
    birs_symb_matchstate sys2 H' bs' ==>
    bir_eval_exp ^bspec_post_tm bs'.bst_environ = SOME bir_val_true``) 
   sys2s;

   val _ = print "\nproving strong postcondition implications for each symbolic execution leaf with the smt solver";
   val strongpostcond_thms = List.map (fn goal =>
    prove(``^goal``, birs_strongpostcond_impl_TAC)) strongpostcond_goals;
   val _ = print " - done\n";

   val Pi_thms_idx = ref 0;
   val Pi_thms = List.map (fn sys2 =>
    let
      val idx = (!Pi_thms_idx);
      (*
      val sys2 = List.nth(sys2s, idx);
      *)
      val _ = print ("proving leaf #" ^ (Int.toString idx) ^ "\n");
      val _ = Pi_thms_idx := idx + 1;
    in
    prove(``
     sys1 = ^sys1 ==>
     sys2 = ^sys2 ==>
     birs_symb_matchstate sys1 H bs ==>
     P_bircont ^birenvtyl_tm ^bspec_pre_tm (birs_symb_to_concst bs) ==>
     symb_interpr_ext H' H ==>
     birs_symb_matchstate sys2 H' bs' ==>
     Q_bircont ^birs_state_end_lbl_tm (set ^prog_vars_list_tm) ^bspec_post_tm
      (birs_symb_to_concst bs) (birs_symb_to_concst bs')``,

    REPEAT STRIP_TAC >>
    Q_bircont_SOLVE3CONJS_TAC prog_vars_thm >> (* val varset_thm = prog_vars_thm; *)
    `birs_symb_matchstate sys1 H' bs` by
     METIS_TAC [bir_symb_soundTheory.birs_symb_matchstate_interpr_ext_IMP_matchstate_thm] >>
    FULL_SIMP_TAC std_ss [P_bircont_thm] >>
    METIS_TAC strongpostcond_thms) end)
   sys2s;

   val bprog_Pi_overapprox_Q_thm =
    prove (``Pi_overapprox_Q
     (bir_symb_rec_sbir ^bprog_tm)
     (P_bircont ^birenvtyl_tm ^bspec_pre_tm)
     (birs_symb_to_symbst ^birs_state_init_pre_tm) (IMAGE birs_symb_to_symbst ^Pi_f)
     (Q_bircont ^birs_state_end_lbl_tm (set ^prog_vars_list_tm) ^bspec_post_tm)``,

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
        (REWRITE_RULE [birs_rulesTheory.birs_symb_exec_def] analysis_thm));

   val bir_abstract_jgmt_rel_thm =
    (MATCH_MP
     (MATCH_MP prop_holds_TO_abstract_jgmt_rel_thm analysis_L_NOTIN_thm)
     (REWRITE_RULE [] bprog_prop_holds_thm));

   val abstract_jgmt_rel_thm =
    prove (``abstract_jgmt_rel (bir_ts ^bprog_tm)
     (^bir_init_lbl_tm) {^bir_end_lbl_tm}
     (\st. bir_exec_to_labels_triple_precond st ^bspec_pre_tm ^bprog_tm)
     (\st st'. bir_exec_to_labels_triple_postcond st'
     (\l. if l = ^bir_end_lbl_tm
          then ^bspec_post_tm
          else bir_exp_false) ^bprog_tm)``,

    MATCH_MP_TAC (REWRITE_RULE
     [boolTheory.AND_IMP_INTRO] abstract_jgmt_rel_bir_exec_to_labels_triple_thm) >>
    SIMP_TAC std_ss [] >>
    EXISTS_TAC birenvtyl_tm >>
    CONJ_TAC >- (
     (* bpre subset *)
     REWRITE_TAC [bspec_pre_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_list_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT] >>
     EVAL_TAC
    ) >>
    CONJ_TAC >- (
     (* bpost subset *)
     REWRITE_TAC [bspec_post_def] >>
     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_list_def] >>
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
    (^bir_init_lbl_tm) {^bir_end_lbl_tm} {}
    ^bspec_pre_tm
    (\l. if l = ^bir_end_lbl_tm
         then ^bspec_post_tm
         else bir_exp_false)``,

    `{^bir_end_lbl_tm} <> {}` by fs [] >>
    MP_TAC ((Q.SPECL [
     `^bir_init_lbl_tm`,
      `{^bir_end_lbl_tm}`,
      `^bspec_pre_tm`,
      `\l. if l = ^bir_end_lbl_tm
           then ^bspec_post_tm
           else bir_exp_false`
    ] o SPEC bprog_tm o INST_TYPE [Type.alpha |-> Type`:'observation_type`])
    abstract_jgmt_rel_bir_cont) >>
    rw [] >>
    METIS_TAC [abstract_jgmt_rel_thm]);
 in
   bspec_cont_thm
 end (* let *)

fun bir_symb_transfer_thm
 bir_prog_def init_addr_def end_addr_def
 bspec_pre_def bspec_post_def
 birenvtyl_def prog_vars_list_def
 symb_analysis_thm pcond_gen_inst_o prog_vars_thm =
 let
   val init_addr_tm = (snd o dest_eq o concl) init_addr_def;
   val end_addr_tm = (snd o dest_eq o concl) end_addr_def;
   val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_pre_def;
   val bspec_post_tm = (lhs o snd o strip_forall o concl) bspec_post_def;
 in
   bir_symb_transfer
     init_addr_tm end_addr_tm
     bspec_pre_tm bspec_post_tm
     bir_prog_def birenvtyl_def
     bspec_pre_def bspec_post_def prog_vars_list_def
     symb_analysis_thm pcond_gen_inst_o prog_vars_thm
 end (* let *)

end (* local *)

local
  open HolKernel boolLib Parse bossLib;
  open markerTheory;
  open distribute_generic_stuffLib;
  open bir_programSyntax bir_program_labelsTheory;
  open bir_immTheory bir_valuesTheory bir_expTheory;
  open bir_tsTheory bir_bool_expTheory bir_programTheory;
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
  open birsSyntax;
  open bir_symb_sound_coreTheory;
  open symb_recordTheory;
  open symb_interpretTheory;
  open pred_setTheory;
  open program_logicSimps;
  open bir_env_oldTheory;
  open bir_program_varsTheory;
  open distribute_generic_stuffTheory;
  open bir_immSyntax;
in

fun bir_symb_transfer_two
 init_addr_tm end_addr_1_tm end_addr_2_tm
 bspec_pre_tm bspec_post_1_tm bspec_post_2_tm
 bir_prog_def birenvtyl_def
 bspec_pre_def bspec_post_1_def bspec_post_2_def prog_vars_list_def
 symb_analysis_thm pcond_gen_inst_o prog_vars_thm =
 let
   val pcond_gen_inst =
     case pcond_gen_inst_o of
         SOME x => x
       | NONE => ``BExp_Const (Imm1 1w)``;
   val (bsysprecond_thm, symb_analysis_thm) =
     birs_transferLib.prepare_transfer
       birenvtyl_def
       pcond_gen_inst
       ((lhs o snd o strip_forall o concl) bspec_pre_def)
       symb_analysis_thm;

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
   
   val (sys_i, L_s, Pi_f) = (get_birs_sysLPi o concl) symb_analysis_thm;
   
   val analysis_L_NOTIN_thm_1 = prove (``^birs_state_end_lbl_1_tm NOTIN ^L_s``,
     REWRITE_TAC [birs_auxTheory.bir_pc_set_lbls_IN_thm] >> EVAL_TAC);
   val analysis_L_NOTIN_thm_2 = prove (``^birs_state_end_lbl_2_tm NOTIN ^L_s``,
     REWRITE_TAC [birs_auxTheory.bir_pc_set_lbls_IN_thm] >> EVAL_TAC);
   
   val birs_state_init_pre_EQ_thm =
    prove (``^(sys_i) = ^birs_state_init_pre_tm``,
     REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, bsysprecond_thm] >>
     CONV_TAC (
       computeLib.RESTR_EVAL_CONV [birs_eval_exp_tm] THENC
       REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm] THENC
       birs_auxLib.GEN_match_conv is_birs_eval_exp birs_stepLib.birs_eval_exp_CONV THENC
       EVAL));
   
   val analysis_thm =
    REWRITE_RULE [birs_state_init_pre_EQ_thm, GSYM bir_prog_def] symb_analysis_thm;

   val birenvtyl_EVAL_thm =
    (REWRITE_CONV [
     birenvtyl_def,
     bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
     bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL)
    birenvtyl_tm;

   val birs_state_thm =
     REWRITE_CONV [birenvtyl_EVAL_thm] birs_state_init_pre_tm;

   val birs_symb_symbols_f_sound_prog_thm =
    (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm)
     bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

   val birs_prop_transfer_thm =
    (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm
     birs_symb_symbols_f_sound_prog_thm);

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
     CONV_TAC (RAND_CONV (bir_exp_typecheckLib.type_of_bir_exp_gen_CONV)) >>
     SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES]) >>
    POP_ASSUM (fn thm => FULL_SIMP_TAC std_ss [thm]));

  val sys1 = (snd o dest_eq o concl o REWRITE_CONV [bsysprecond_thm]) birs_state_init_pre_tm;
  val sys2s = pred_setSyntax.strip_set Pi_f;

  val sys2ps = [
   (List.nth (sys2s,0), bspec_post_1_tm, birs_state_end_lbl_1_tm),
   (List.nth (sys2s,1), bspec_post_2_tm, birs_state_end_lbl_2_tm)
  ];

  val strongpostcond_goals = List.map (fn (sys2,post_tm,_) => ``
   sys1 = ^sys1 ==>
   sys2 = ^sys2 ==>
   birs_symb_matchstate sys1 H' bs ==>
   bir_eval_exp ^bspec_pre_tm bs.bst_environ = SOME bir_val_true ==>
   birs_symb_matchstate sys2 H' bs' ==>
   bir_eval_exp ^post_tm bs'.bst_environ = SOME bir_val_true``) 
  sys2ps;

  val strongpostcond_thms = List.map (fn goal =>
   prove(``^goal``, birs_strongpostcond_impl_TAC))
  strongpostcond_goals;

  val Pi_thms = List.map (fn (sys2,post_tm,birs_state_end_lbl_tm) =>
   prove(``
    sys1 = ^sys1 ==>
    sys2 = ^sys2 ==>
    birs_symb_matchstate sys1 H bs ==>
    P_bircont ^birenvtyl_tm ^bspec_pre_tm (birs_symb_to_concst bs) ==>
    symb_interpr_ext H' H ==>
    birs_symb_matchstate sys2 H' bs' ==>
    Q_bircont ^birs_state_end_lbl_tm (set ^prog_vars_list_tm) ^post_tm
     (birs_symb_to_concst bs) (birs_symb_to_concst bs')``,
  
   REPEAT STRIP_TAC >>
  
   FULL_SIMP_TAC (std_ss) [Q_bircont_thm] >>
   CONJ_TAC >- (
    REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
   ) >>
  
   CONJ_TAC >- (
    REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
   )  >>
  
   CONJ_TAC >- (
    PAT_X_ASSUM ``A = B`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    PAT_X_ASSUM ``A = B`` (K ALL_TAC) >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def, prog_vars_thm] >>
  
    IMP_RES_TAC birs_env_vars_are_initialised_IMP_thm >>
    POP_ASSUM (K ALL_TAC) >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ((snd o dest_eq o concl) prog_vars_thm)) >>
    POP_ASSUM (MATCH_MP_TAC) >>
  
    REPEAT (POP_ASSUM (K ALL_TAC)) >>
  
    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm, birs_auxTheory.birs_exps_of_senv_thm] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_gen_env_def, birs_gen_env_fun_def, birs_gen_env_fun_def, bir_envTheory.bir_env_lookup_def] >>
  
    FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_auxTheory.birs_exps_of_senv_COMP_thm] >>
    CONV_TAC (RATOR_CONV (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_exp``] THENC SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL))) >>
    CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_program``] THENC SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [] THENC EVAL)) >>
    REWRITE_TAC [birs_env_vars_are_initialised_INSERT_thm, birs_env_vars_are_initialised_EMPTY_thm, birs_env_var_is_initialised_def] >>
  
    EVAL_TAC >>
    SIMP_TAC (std_ss++holBACore_ss++pred_setLib.PRED_SET_ss) [] >>
    EVAL_TAC) >>
  
    `birs_symb_matchstate sys1 H' bs` by
     METIS_TAC [bir_symb_soundTheory.birs_symb_matchstate_interpr_ext_IMP_matchstate_thm] >>
    FULL_SIMP_TAC std_ss [P_bircont_thm] >>
    METIS_TAC strongpostcond_thms))
 sys2ps;

 val bprog_Q_birconts_tm =
  ``\st st'.
     Q_bircont ^(#3 (List.nth (sys2ps,0))) (set ^prog_vars_list_tm)
      ^(#2 (List.nth (sys2ps,0))) st st' \/
     Q_bircont ^(#3 (List.nth (sys2ps,1))) (set ^prog_vars_list_tm)
      ^(#2 (List.nth (sys2ps,1))) st st'``;

 val bprog_Pi_overapprox_Q_thm =
  prove (``Pi_overapprox_Q
   (bir_symb_rec_sbir ^bprog_tm)
   (P_bircont ^birenvtyl_tm ^bspec_pre_tm)
   (birs_symb_to_symbst ^birs_state_init_pre_tm) (IMAGE birs_symb_to_symbst ^Pi_f)
   ^bprog_Q_birconts_tm``,
  
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
     (REWRITE_RULE [birs_rulesTheory.birs_symb_exec_def] analysis_thm));

 val bir_abstract_jgmt_rel_thm =
  (MATCH_MP
   (MATCH_MP
     (MATCH_MP prop_holds_TO_abstract_jgmt_rel_two_thm analysis_L_NOTIN_thm_1) analysis_L_NOTIN_thm_2)
   (REWRITE_RULE [] bprog_prop_holds_thm));

 val abstract_jgmt_rel_thm =
  prove (``abstract_jgmt_rel (bir_ts ^bprog_tm)
   (BL_Address (Imm64 ^init_addr_tm))
   {BL_Address (Imm64 ^end_addr_1_tm); BL_Address (Imm64 ^end_addr_2_tm);}
   (\st. bir_exec_to_labels_triple_precond st ^bspec_pre_tm ^bprog_tm)
   (\st st'. bir_exec_to_labels_triple_postcond st'
   (\l. if l = BL_Address (Imm64 ^end_addr_1_tm) then ^bspec_post_1_tm
        else if l = BL_Address (Imm64 ^end_addr_2_tm) then ^bspec_post_2_tm
        else bir_exp_false) ^bprog_tm)``,
  
   MATCH_MP_TAC (REWRITE_RULE
    [boolTheory.AND_IMP_INTRO] abstract_jgmt_rel_bir_exec_to_two_labels_triple_thm) >>
   SIMP_TAC std_ss [] >>
   EXISTS_TAC birenvtyl_tm >>
   CONJ_TAC >- rw [] >>
   CONJ_TAC >- (
    (* bpre subset *)
    REWRITE_TAC [bspec_pre_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_list_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT] >>
    EVAL_TAC
   ) >>
   CONJ_TAC >- (
    (* bpost_1 subset *)
    REWRITE_TAC [bspec_post_1_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_list_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
   ) >>
   CONJ_TAC >- (
    (* bpost_2 subset *)
    REWRITE_TAC [bspec_post_2_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM prog_vars_thm, prog_vars_list_def] >>
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++holBACore_ss) [listTheory.MEM, pred_setTheory.IN_INSERT]
   ) >>
   CONJ_TAC >- (
    (* bpost_1 is bool *)
    REWRITE_TAC [bspec_post_1_def] >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def]
   ) >>
   CONJ_TAC >- (
    (* bpost_2 is bool *)
    REWRITE_TAC [bspec_post_2_def] >>
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
   (BL_Address (Imm64 ^init_addr_tm)) {BL_Address (Imm64 ^end_addr_1_tm); BL_Address (Imm64 ^end_addr_2_tm)} {}
   ^bspec_pre_tm
   (\l. if l = BL_Address (Imm64 ^end_addr_1_tm) then ^bspec_post_1_tm
        else if l = BL_Address (Imm64 ^end_addr_2_tm) then ^bspec_post_2_tm
        else bir_exp_false)``,
  
  `{BL_Address (Imm64 ^end_addr_1_tm); BL_Address (Imm64 ^end_addr_2_tm)} <> {}` by fs [] >>
  MP_TAC ((Q.SPECL [
    `BL_Address (Imm64 ^init_addr_tm)`,
    `{BL_Address (Imm64 ^end_addr_1_tm); BL_Address (Imm64 ^end_addr_2_tm)}`,
    `^bspec_pre_tm`,
    `\l. if l = BL_Address (Imm64 ^end_addr_1_tm) then ^bspec_post_1_tm
        else if l = BL_Address (Imm64 ^end_addr_2_tm) then ^bspec_post_2_tm
        else bir_exp_false`
  ] o SPEC bprog_tm o INST_TYPE [Type.alpha |-> Type`:'observation_type`])
     abstract_jgmt_rel_bir_cont) >>
  rw [] >>
  METIS_TAC [abstract_jgmt_rel_thm]);

 in
   bspec_cont_thm
 end (* let *)

fun bir_symb_transfer_two_thm
  bir_prog_def 
  init_addr_def end_addr_1_def end_addr_2_def  
  bspec_pre_def bspec_post_1_def bspec_post_2_def
  birenvtyl_def prog_vars_list_def
  symb_analysis_thm pcond_gen_inst_o prog_vars_thm =
  let
    val init_addr_tm = (snd o dest_eq o concl) init_addr_def;
    val end_addr_1_tm = (snd o dest_eq o concl) end_addr_1_def;
    val end_addr_2_tm = (snd o dest_eq o concl) end_addr_2_def;
    val bspec_pre_tm = (lhs o snd o strip_forall o concl) bspec_pre_def;
    val bspec_post_1_tm = (lhs o snd o strip_forall o concl) bspec_post_1_def;
    val bspec_post_2_tm = (lhs o snd o strip_forall o concl) bspec_post_2_def;
  in
    bir_symb_transfer_two
     init_addr_tm end_addr_1_tm end_addr_2_tm
     bspec_pre_tm bspec_post_1_tm bspec_post_2_tm
     bir_prog_def birenvtyl_def
     bspec_pre_def bspec_post_1_def bspec_post_2_def prog_vars_list_def
     symb_analysis_thm pcond_gen_inst_o prog_vars_thm
  end (* let *)

end (* local *)

end (* structure *)
