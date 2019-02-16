open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_auxiliaryTheory;
open bir_program_multistep_propsTheory;
open bir_programSyntax;
open bir_envSyntax;

open bir_exec_blockLib;
open bir_exec_typingLib;

open numSyntax;
open HolBACoreSimps;


val debug_trace = ref (1:int)
val _ = register_trace ("bir_exec.DEBUG_LEVEL", debug_trace, 2)



structure bir_execLib =
struct


(*
  bir_exec_prog_step_n var_eq_thm thm

  bir_exec_prog_step_iter (bir_exec_prog_step_n var_eq_thm) thm

  bir_exec_prog prog 1
  bir_exec_prog prog 2
  bir_exec_prog prog 3
  bir_exec_prog prog 4
  bir_exec_prog prog 5
  bir_exec_prog prog 6
  bir_exec_prog prog 7
*)



  fun bir_exec_is_state_triple t =
    if not (is_pair t) orelse not (is_pair (snd (dest_pair t))) then false
    else
                               let
                                 val (_,x) = dest_pair t;
                                 val (n_acc,s) = dest_pair x;
                               in
                                 is_numeral n_acc andalso
                                 is_bir_state s andalso
                                 let val (pc,env,_) = dest_bir_state s in
                                   is_BEnv env andalso
                                   is_bir_programcounter pc andalso
                                   let val (l,i) = dest_bir_programcounter pc in
                                     is_numeral i andalso
                                     (is_BL_Label l orelse is_BL_Address l)
                                   end
                                 end
                               end;


  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_multistep_props"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exec_step_n_acc_tm,  mk_bir_exec_step_n_acc, dest_bir_exec_step_n_acc, is_bir_exec_step_n_acc)  = syntax_fns3 "bir_exec_step_n_acc";

  val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);
  fun bir_exec_prog_step_n_conv block_thm_map var_eq_thm =
    let
      val is_tm_fun = (fn t => is_bir_exec_step_n_acc t andalso
                               let
                                 val (_,n,x) = dest_bir_exec_step_n_acc t;
                               in
                                 is_numeral n andalso
                                 bir_exec_is_state_triple x
                               end
                      );
      val check_tm_fun = (fn t => is_tm_fun t orelse
                                  bir_exec_is_state_triple t
                         );
      fun conv t =
        let
          val (_,n,x) = dest_bir_exec_step_n_acc t;
          val (_,x) = dest_pair x;
          val (_,s) = dest_pair x;
          val is_terminated_thm = (SIMP_CONV (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def])
                                      (mk_bir_state_is_terminated s);

          val n_eq_0_tm = (mk_eq (n, mk_numeral (Arbnum.fromInt 0)));
          val n_eq_0_thm = SIMP_CONV arith_ss [] n_eq_0_tm;

          val thm2 = (REWRITE_CONV [Once bir_exec_step_n_acc_def, is_terminated_thm, n_eq_0_thm]) t;

          val thm3 = CONV_RULE (RAND_CONV (bir_exec_prog_step_conv block_thm_map var_eq_thm)) thm2;
          val thm4 = CONV_RULE (RAND_CONV (SIMP_CONV (arith_ss) [LET_DEF])) thm3;
        in
          thm4
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;


  fun bir_exec_prog_step_iter step_n_conv thm =
    let
      val _ = if (!debug_trace >= 1) then (print "!") else ();
      val t = (snd o dest_eq o concl) thm;
      val thm1 = (step_n_conv THENC (REWRITE_CONV [OPT_CONS_REWRS])) t;
      val thm2 = TRANS thm thm1;
      val thm = thm2;
    in
      (bir_exec_prog_step_iter step_n_conv thm)
      handle UNCHANGED =>
      (
        if (!debug_trace >= 1) then (print "done\n") else ();
        let
          val result = (snd o dest_eq o concl) thm;
          fun check_thm_fun _ = bir_exec_is_state_triple result;
          fun extract_print_tm_fun _ = result;
        in
          GEN_check_thm check_thm_fun extract_print_tm_fun thm
        end
      )
    end;




  fun bir_exec_prog_normalize prog =
    (snd o dest_eq o concl o (REWRITE_CONV [bir_program_labelsTheory.BL_Address_HC_def])) prog;


  fun bir_exec_prog name prog n_max =
    let
      val _ = if (!debug_trace >= 1) then (print "preprocessing starts\n") else ();

      val prog = bir_exec_prog_normalize prog handle UNCHANGED => prog;
      val prog_def = Define [QUOTE ("bir_exec_prog_" ^ name ^ " = "), ANTIQUOTE prog];
      val prog_const = (fst o dest_eq o concl) prog_def;

      val block_thm_map = gen_block_thm_map prog_def;

      val n = numSyntax.mk_numeral (Arbnumcore.fromInt n_max);
      val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog_const``;

      val vars = gen_vars_of_prog prog;
      val var_eq_thm = gen_var_eq_thm vars;

      val env = bir_exec_env_initd_env vars;

      val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;

      val exec_term = ``bir_exec_step_n ^prog_const ^state ^n``;
      val thm = REWRITE_CONV [GSYM bir_exec_step_n_acc_eq_thm] exec_term;

      val step_n_conv = (bir_exec_prog_step_n_conv block_thm_map var_eq_thm);

      val _ = if (!debug_trace >= 1) then (print "execution starts\n") else ();
    in
      (CONV_RULE (RAND_CONV (REWRITE_CONV [CONJUNCT1 REVERSE_DEF])))
      (bir_exec_prog_step_iter step_n_conv thm)
    end;


  fun bir_exec_prog_result name prog n_max =
    let
      val exec_thm = bir_exec_prog name prog n_max;
      val result_t = (snd o dest_eq o concl) exec_thm;
      val (ol, x)  = dest_pair result_t;
      val (n, s2)  = dest_pair x;
    in
      (ol, n, s2)
    end;

  local
    open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;
open bir_extra_expsTheory;
open bir_interval_expTheory;
open bir_program_labelsTheory;

open finite_mapSyntax;
open pairSyntax;


  in
    fun bir_exec_typecheck_prog_result prog =
      let
        val prog_typed_conv = [
			    bir_is_well_typed_program_def,bir_is_well_typed_block_def,bir_is_well_typed_stmtE_def,
			    bir_is_well_typed_stmtB_def,bir_is_well_typed_label_exp_def,
			    type_of_bir_exp_def,bir_var_type_def,bir_type_is_Imm_def,type_of_bir_imm_def,
			    bir_extra_expsTheory.BExp_Aligned_type_of,BExp_unchanged_mem_interval_distinct_type_of,
			    bir_exp_memTheory.bir_number_of_mem_splits_REWRS, BType_Bool_def, bir_exp_true_def, bir_exp_false_def, BExp_MSB_type_of,
			    bir_nzcv_expTheory.BExp_nzcv_ADD_DEFS, bir_nzcv_expTheory.BExp_nzcv_SUB_DEFS, bir_immTheory.n2bs_def, bir_extra_expsTheory.BExp_word_bit_def,
			    BExp_Align_type_of, BExp_ror_type_of, BExp_LSB_type_of, BExp_word_bit_exp_type_of,
			    bir_nzcv_expTheory.BExp_ADD_WITH_CARRY_type_of, BExp_word_reverse_type_of,
                            BExp_ror_exp_type_of
			    ];
        val prog_valid_conv = [
			     bir_program_valid_stateTheory.bir_is_valid_program_def,
			     bir_program_valid_stateTheory.bir_program_is_empty_def,
			     bir_program_valid_stateTheory.bir_is_valid_labels_def,
			     bir_labels_of_program_def,BL_Address_HC_def
			     ];

        val thm = prove(``bir_is_well_typed_program ^prog``, SIMP_TAC (srw_ss()) (prog_typed_conv))
                  handle _ => raise ERR "bir_exec_typecheck_prog_result" "typechecking of program failed";

        val thm = prove(``bir_is_valid_program ^prog``, SIMP_TAC (srw_ss()) (prog_valid_conv))
                  handle _ => raise ERR "bir_exec_typecheck_prog_result" "program is not valid - must be non-empty list of blocks with distinct labels";
      in
        ()
      end;
  end;


end
