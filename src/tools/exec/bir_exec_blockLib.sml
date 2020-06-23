structure bir_exec_blockLib =
struct

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
  open numSyntax;

  open listTheory;
  open listSyntax;
  open wordsLib;

  open bir_blockCollectionLib;

  open bir_program_valid_stateTheory;
  open bir_program_labelsTheory;

  (*
    val t = ``bir_exec_step ^prog_const ^state``;

    bir_exec_prog_step_conv block_thm_map var_eq_thms t
  *)

  fun gen_block_thm_map prog_l_def valid_prog_thm = gen_MEM_thm_block_dict prog_l_def valid_prog_thm;

  (* this only works if the program in the map is the same considered in the term *)
  fun block_thm_map_conv block_thm_map =
    let
      val is_tm_fun = is_bir_get_program_block_info_by_label;
      val check_tm_fun = not o is_bir_get_program_block_info_by_label;
      fun conv t =
        let
          (* lookup the corresponding block thm *)
          val (_,l) = dest_bir_get_program_block_info_by_label t;
          val cur_lbl = (snd o dest_eq o concl o EVAL) l;
          val block_thm = case lookup_block_dict block_thm_map cur_lbl of
                             SOME x => x
                           | NONE => raise UNCHANGED;
        in
          SIMP_CONV (list_ss++bir_TYPES_ss) [block_thm] t
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;


(*
for now, we're taking single steps, not whole blocks
*)
  fun bir_exec_prog_step_conv block_thm_map var_eq_thms =
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
          (* prepare search for block *)
          val thm1 = (
                    (SIMP_CONV (std_ss++bir_TYPES_ss) [
                         bir_exec_step_def,
                         bir_get_current_statement_def,
                         bir_state_is_terminated_def,
                         bir_state_set_failed_def])
                   ) t;

          (* get block and current statement *)
          val thm1_1 = CONV_RULE (RAND_CONV (
                    (block_thm_map_conv block_thm_map) THENC
                    (SIMP_CONV (list_ss++bir_TYPES_ss) [])
                   )) thm1;

          (* open statement effects *)
          val thm1_2 = CONV_RULE (RAND_CONV (
                    (REWRITE_CONV [
                         bir_exec_stmt_assign_def,
                         bir_exec_stmt_assert_def,
                         bir_exec_stmt_assume_def,
                         bir_exec_stmt_observe_def,
                         bir_exec_stmt_halt_def,
                         bir_exec_stmt_jmp_def,
                         bir_exec_stmt_cjmp_def,
                         bir_exec_stmtB_def,
                         bir_exec_stmtE_def,
                         bir_exec_stmt_def
                       ])
                   )) thm1_1;

          (* evaluate expressions (bir_eval_exp and bir_eval_label_exp) *)
          val thm1_3 = CONV_RULE (RAND_CONV (
                    (* apply MAP, when introduced by observation statements *)
                    (REWRITE_CONV [MAP]) THENC
                    (* evaluate the expressions *)
                    (bir_exec_exp_conv var_eq_thms) THENC
                    (* open the evaluation of label expressions *)
                    (* (additionally for cjmp: determine which branch to take) *)
                    (SIMP_CONV (std_ss++WORD_ss) [
                         bir_dest_bool_val_def,
                         bir_eval_label_exp_def]) THENC
                    (* evaluate the new label expressions *)
                    (bir_exec_exp_conv var_eq_thms) THENC
                    (* resolve cases *)
                    CASE_SIMP_CONV THENC
                    (* finally update the environment *)
                    (bir_exec_env_write_conv var_eq_thms)
                   )) thm1_2;

          (* control flow *)
          val thm_pre_pc_upd = thm1_3;
          val thm4 =
            (* try jmp_to_label *)
            let
              (* lookup the block thm for the jump target *)
              val jutola = ((GEN_find_subterm is_bir_exec_stmt_jmp_to_label) o
                             snd o dest_eq o concl
                            ) thm_pre_pc_upd;
              val (prog_tm,l,_) = dest_bir_exec_stmt_jmp_to_label jutola;
              val cur_lbl = l;
              val block_thm_to = case lookup_block_dict block_thm_map cur_lbl of
                             SOME x => x
                           | NONE =>
                                   (* maybe we jump outside? *)
                                   let
                                     val mem_labels_thm = EVAL ``MEM ^cur_lbl (bir_labels_of_program ^prog_tm)``;
                                     val _ = if (snd o dest_eq o concl) mem_labels_thm = F then () else
                                              raise ERR "bir_exec_prog_step_conv" ("label is not in the dictionary and cannot resolve: " ^ (term_to_string jutola));
                                   in
                                     (REWRITE_RULE []) mem_labels_thm
                                   end;

              (* compute program counter for the next block *)
              val thm2 = CONV_RULE (RAND_CONV (REWRITE_CONV [
                                block_thm_to,
                                bir_exec_stmt_jmp_to_label_def,
                                bir_block_pc_def])) thm_pre_pc_upd;

              (* cleanup bir_state_t record (for updated pc) *)
              val thm3 = CONV_RULE (RAND_CONV (SIMP_CONV (std_ss++bir_TYPES_ss) [])) thm2;
            in
              thm3
            end
            handle UNCHANGED =>
            (* if jmp_to_label is not present *)
            (* pc_next update and finalize *)
            (* notice: observation functions could get applied here, for example list functions according to list_ss *)
            CONV_RULE (RAND_CONV (SIMP_CONV (list_ss++bir_TYPES_ss)
               [LET_DEF, bir_pc_next_def, bir_state_is_terminated_def]
             )) thm_pre_pc_upd
            ;
        in
          thm4
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;



end
