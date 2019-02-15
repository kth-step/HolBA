open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_programTheory;
open bir_programSyntax;
open bir_valuesTheory;

open HolBACoreSimps;

open bir_exec_auxLib;
open bir_exec_envLib;
open bir_exec_expLib;

open optionSyntax;
open pairSyntax;
open listTheory;
open wordsLib;

structure bir_exec_blockLib =
struct


(*
  val t = ``bir_exec_step ^prog ^state``;

  bir_exec_prog_step_conv var_eq_thm t
*)



  val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);
  fun bir_exec_prog_step_conv var_eq_thm =
    let
      val is_tm_fun = is_bir_exec_step;
      val check_tm_fun = (fn t => is_pair t andalso
                                  let
                                    val (ov, st) = dest_pair t;
                                  in
                                    (is_none ov orelse is_some ov) andalso
                                    (is_bir_state st)
                                  end);
      fun conv t =
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
                      (list_ss++WORD_ss++HolBACoreSimps.holBACore_ss) [
                            bir_program_labelsTheory.bir_labels_of_program_REWRS,
                            bir_block_pc_def])) thm1_1;

          val thm2 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (list_ss++HolBACoreSimps.holBACore_ss) [LET_DEF])) thm1_2;

          val thm3 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (arith_ss++bir_pc_ss) [bir_pc_next_def])) thm2;
        in
          thm3
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;



end
