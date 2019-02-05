open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_programTheory;
open bir_programSyntax;

open bir_program_multistep_propsTheory;

open bir_exec_envLib;
open bir_exec_expLib;
open bir_exec_typingLib;

open bir_auxiliaryTheory;
open HolBACoreSimps;

open pairSyntax;

open listTheory;

open wordsLib;


structure bir_execLib =
struct


(*
  val t = ``bir_exec_step ^prog ^state``;

  bir_exec_prog_step_conv_help var_eq_thm t

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

val t = ``bir_exec_step
          (BirProgram
             [<|bb_label := BL_Label "entry";
                bb_statements :=
                  [BStmt_Assign (BVar "bit1" BType_Bool)
                     (BExp_MSB Bit32
                        (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm32 258w)))|>;
              <|bb_label := BL_Address (Imm32 258w);
                bb_statements :=
                  [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                     (BExp_Const (Imm32 25w));
                   BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                     (BExp_Const (Imm32 7w))];
                bb_last_statement :=
                  BStmt_CJmp
                    (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 7w))
                       (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                    (BLE_Label (BL_Address (Imm32 260w)))
                    (BLE_Label (BL_Address (Imm32 262w)))|>;
              <|bb_label := BL_Address (Imm32 260w);
                bb_statements :=
                  [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                        (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                bb_last_statement :=
                  BStmt_Halt (BExp_Const (Imm32 1w))|>;
              <|bb_label := BL_Address (Imm32 262w);
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Halt (BExp_Const (Imm32 0w))|>])
          <|bst_pc :=
              <|bpc_label := BL_Address (Imm32 258w); bpc_index := 2|>;
            bst_environ :=
              BEnv
                (FEMPTY |+
                 ("R1",BType_Imm Bit32,SOME (BVal_Imm (Imm32 0w))) |+
                 ("bit1",BType_Imm Bit1,SOME (BVal_Imm (Imm1 0w))) |+
                 ("R3",BType_Imm Bit32,SOME (BVal_Imm (Imm32 25w))) |+
                 ("R2",BType_Imm Bit32,SOME (BVal_Imm (Imm32 7w))));
            bst_status := BST_Running|>``;


  val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);
  fun bir_exec_prog_step_conv_help var_eq_thm t =
    if not (is_bir_exec_step t) then
      raise UNCHANGED
    else
      let
        val thm1 = (
                    (SIMP_CONV (list_ss++WORD_ss++bir_TYPES_ss) [
                         bir_exec_stmt_declare_def,
                         bir_exec_stmt_assign_def,
                         bir_exec_stmt_assert_def,
                         bir_exec_stmt_assume_def,
                         bir_exec_stmt_observe_def,
                         bir_exec_stmt_halt_def,
                         bir_exec_stmt_jmp_def,
                         bir_exec_stmt_cjmp_def,
                         bir_exec_stmtB_def,
                         bir_exec_stmtE_def,
                         bir_exec_stmt_def,
                         bir_exec_step_def,
                         bir_state_is_terminated_def,
                         bir_state_set_failed_def,
                         bir_get_current_statement_def,
                         bir_get_program_block_info_by_label_def,
                         INDEX_FIND_def
                       ])
                   ) t;

        val thm1_1 = CONV_RULE (RAND_CONV (
                    (bir_exec_exp_conv var_eq_thm) THENC
                    (SIMP_CONV (list_ss++WORD_ss++bir_TYPES_ss) [
                         bir_dest_bool_val_def,
                         bir_exec_stmt_jmp_to_label_def,
                         bir_eval_label_exp_def]) THENC
                    (bir_exec_exp_conv var_eq_thm) THENC
                    (bir_exec_env_write_conv var_eq_thm) THENC
                    (SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                        bir_valuesTheory.BType_Bool_def]) (* todo here? *)
                   )) thm1;

        val thm1_2 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (list_ss++HolBACoreSimps.holBACore_ss) [
                            bir_program_labelsTheory.bir_labels_of_program_REWRS,
                            bir_block_pc_def])) thm1_1;

        val thm2 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (list_ss++HolBACoreSimps.holBACore_ss) [LET_DEF])) thm1_2;

        val thm3 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (arith_ss++bir_pc_ss) [bir_pc_next_def])) thm2;
      in
        thm3
      end;

  fun GEN_bir_exec_step_conv conv tm =
    if is_bir_exec_step tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_exec_step_conv conv)) THENC
         (RATOR_CONV (GEN_bir_exec_step_conv conv))) tm
    else
      raise UNCHANGED
    ;

  val bir_exec_prog_step_conv = GEN_bir_exec_step_conv o bir_exec_prog_step_conv_help;



  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_multistep_props"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exec_step_n_acc_tm,  mk_bir_exec_step_n_acc, dest_bir_exec_step_n_acc, is_bir_exec_step_n_acc)  = syntax_fns3 "bir_exec_step_n_acc";
  fun bir_exec_prog_step_n var_eq_thm thm =
    let
      val exec_term = (snd o dest_eq o concl) thm;
    in if not (is_bir_exec_step_n_acc exec_term) then raise UNCHANGED else
    let
      val (_,n,x) = dest_bir_exec_step_n_acc exec_term;
      val (_,x) = dest_pair x;
      val (_,s) = dest_pair x;
    in
      if not (numSyntax.is_numeral n) then
        raise UNCHANGED
      else
        let
          val is_terminated_thm = ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL)
                                      (mk_bir_state_is_terminated s);

          val thm2 = CONV_RULE (RAND_CONV (
                 (REWRITE_CONV [Once bir_exec_step_n_acc_def, is_terminated_thm, EVAL ``^n = 0:num``])
               )) thm;

          val thm3 = CONV_RULE (RAND_CONV (bir_exec_prog_step_conv var_eq_thm)) thm2;
          val thm4 = CONV_RULE (RAND_CONV (SIMP_CONV (arith_ss) [LET_DEF])) thm3;

        in
          thm4
        end
    end end;


  fun bir_exec_prog_step_iter step_n_rule thm =
    let
      val thm1 = step_n_rule thm;
      val thm2 = CONV_RULE (RAND_CONV (REWRITE_CONV [OPT_CONS_REWRS])) thm1;
      val thm = thm2;
    in
      (bir_exec_prog_step_iter step_n_rule thm)
      handle UNCHANGED => thm
    end;




  fun bir_exec_prog_normalize prog =
    (snd o dest_eq o concl o (REWRITE_CONV [bir_program_labelsTheory.BL_Address_HC_def])) prog;


  fun bir_exec_prog prog n_max =
    let
      val prog = bir_exec_prog_normalize prog handle UNCHANGED => prog;

      val n = numSyntax.mk_numeral (Arbnumcore.fromInt n_max);
      val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog``;

      val vars = gen_vars_of_prog prog;
      val var_eq_thm = gen_var_eq_thm vars;

      val env = bir_exec_env_initd_env vars;

      val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;

      val exec_term = ``bir_exec_step_n ^prog ^state ^n``;
      val thm = REWRITE_CONV [GSYM bir_exec_step_n_acc_eq_thm] exec_term;

      val step_n_rule = (bir_exec_prog_step_n var_eq_thm);
    in
      (CONV_RULE (RAND_CONV (REWRITE_CONV [CONJUNCT1 REVERSE_DEF])))
      (bir_exec_prog_step_iter step_n_rule thm)
    end;


   fun bir_exec_prog_result prog n_max =
     let
       val exec_thm = bir_exec_prog prog n_max;
       val result_t = (snd o dest_eq o concl) exec_thm;
       val (ol, x)  = dest_pair result_t;
       val (n, s2)  = dest_pair x;
     in
       (ol, n, s2)
     end;

end
