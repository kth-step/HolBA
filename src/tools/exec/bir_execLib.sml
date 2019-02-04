
open bir_programTheory;
open bir_programSyntax;

open bir_program_multistep_propsTheory;

open bir_exec_expLib;
open bir_exec_envLib;

structure bir_execLib =
struct


(*
  val prog = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "bit1" BType_Bool)
                           (BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x102w) "abc";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;

  val n = ``50:num``;

  val pc = ``<| bpc_label := BL_Label "entry" ; bpc_index := 0 |>``;
  val env = ``BEnv (FEMPTY |+ ("bit1", (BType_Bool,      SOME (BVal_Imm (Imm1  0w))))
                           |+ ("R1",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 0w))))
                           |+ ("R2",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 0w))))
                           |+ ("R3",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 0w))))
                   )``;

  val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;

  val exec_term = ``bir_exec_step_n ^prog ^state ^n``;

  val thm = REWRITE_CONV [GSYM bir_exec_step_n_acc_eq_thm] exec_term;

  val var_eq_thm =
    let
      val vars = [``"bit1"``, ``"R1"``, ``"R2"``, ``"R3"``];
    in
      LIST_CONJ (List.map ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL) (List.foldl (fn (v,l) => (List.map (fn v2 => mk_eq(v,v2)) vars)@l) [] vars))
    end;

  val t = ``bir_exec_step ^prog ^state``;



  val t = ``

bir_exec_step
        (BirProgram
           [<|bb_label := BL_Label "entry";
              bb_statements :=
                [BStmt_Assign (BVar "bit1" (BType_Imm Bit1))
                   (BExp_BinPred BIExp_SignedLessThan
                      (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 0w)))];
              bb_last_statement :=
                BStmt_Jmp (BLE_Label (BL_Address (Imm32 258w)))|>;
            <|bb_label := BL_Address (Imm32 258w);
              bb_statements :=
                [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
              bb_last_statement :=
                BStmt_Halt (BExp_Const (Imm32 1w))|>])
        <|bst_pc := <|bpc_label := BL_Label "entry"; bpc_index := 0|>;
          bst_environ :=
            BEnv
              (FEMPTY |+
               ("bit1",BType_Imm Bit1,SOME (BVal_Imm (Imm1 0w))) |+
               ("R1",BType_Imm Bit32,SOME (BVal_Imm (Imm32 0w))) |+
               ("R2",BType_Imm Bit32,SOME (BVal_Imm (Imm32 0w))) |+
               ("R3",BType_Imm Bit32,SOME (BVal_Imm (Imm32 0w))));
          bst_status := BST_Running|>

          ``;

*)


  fun GEN_bir_exec_step_conv conv tm =
    if is_bir_exec_step tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_exec_step_conv conv)) THENC
         (RATOR_CONV (GEN_bir_exec_step_conv conv))) tm
    else
      raise UNCHANGED
    ;


  val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);
  fun bir_exec_prog_step_conv_help var_eq_thm t =
    if not (is_bir_exec_step t) then
      raise UNCHANGED
    else
      let
        val thm1 = (
                    (SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                         bir_exec_stmt_declare_def,
                         bir_exec_stmt_assign_def,
                         bir_exec_stmt_assert_def,
                         bir_exec_stmt_assume_def,
                         bir_exec_stmt_observe_def,
                         bir_exec_stmtB_def,
                         bir_exec_stmt_halt_def,
                         bir_exec_stmt_jmp_to_label_def,
                         bir_eval_label_exp_def,
                         bir_exec_stmt_jmp_def,
                         bir_exec_stmt_cjmp_def,
                         bir_exec_stmtE_def,
                         bir_exec_stmt_def,
                         bir_exec_step_def,
                         bir_state_is_terminated_def,
                         bir_state_set_failed_def,
                         bir_get_current_statement_def,
                         bir_get_program_block_info_by_label_def,
                         listTheory.INDEX_FIND_def
                       ]) THENC
                    (bir_exec_exp_conv) THENC
                    (bir_exec_env_write_conv var_eq_thm) THENC
                    (SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                        bir_valuesTheory.BType_Bool_def(*,
                        bir_env_read_def,
                bir_env_lookup_type_def,
                bir_env_check_type_def,
                FLOOKUP_EMPTY,
                FLOOKUP_UPDATE,
bir_eval_bin_pred_def,
bir_env_lookup_def,
                        var_eq_thm*)])
                   ) t;

        val thm2 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (list_ss++HolBACoreSimps.holBACore_ss) [LET_DEF])) thm1;

        val thm3 = CONV_RULE (RAND_CONV (SIMP_CONV
                      (arith_ss++bir_pc_ss) [bir_pc_next_def])) thm2;
      in
        thm3
      end;


  val bir_exec_prog_step_conv = GEN_bir_exec_step_conv o bir_exec_prog_step_conv_help;



  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_multistep_props"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exec_step_n_acc_tm,  mk_bir_exec_step_n_acc, dest_bir_exec_step_n_acc, is_bir_exec_step_n_acc)  = syntax_fns3 "bir_exec_step_n_acc";
  
open pairSyntax;
  fun bir_exec_prog_step_n var_eq_thm thm =
    let
      val exec_term = (snd o dest_eq o concl) thm;
      val (_,n,x) = dest_bir_exec_step_n_acc exec_term;
      val (_,x) = dest_pair x;
      val (_,s) = dest_pair x;
    in
      if not (numSyntax.is_numeral n) then
        raise UNCHANGED
      else
        let
(*
          val thm1 = if Arbnumcore.<= ((numSyntax.dest_numeral n), (Arbnumcore.fromInt 1)) then
                      thm
                    else
                      GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) empty_rewrites
                        [Once (prove(``^n = (SUC ((^n)-1))``, SIMP_TAC arith_ss []))] thm;
          val exec_term1 = (snd o dest_eq o concl) thm1;



          val thm2 = CONV_RULE (RAND_CONV (SIMP_CONV std_ss [
                        is_terminated_thm,
                        bir_exec_step_n_REWR_0,
                        bir_exec_step_n_REWR_NOT_TERMINATED,
                        bir_exec_step_n_REWR_TERMINATED])) thm1;
*)

          val is_terminated_thm = ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL)
                                      (mk_bir_state_is_terminated s);

          val thm2 = CONV_RULE (RAND_CONV (
                 (REWRITE_CONV [Once bir_exec_step_n_acc_def, is_terminated_thm, EVAL ``^n = 0:num``]) (*THENC
                 (computeLib.RESTR_EVAL_CONV [bir_exec_step_n_acc_tm, bir_exec_step_tm])*)
               )) thm;

          val thm3 = CONV_RULE (RAND_CONV (bir_exec_prog_step_conv var_eq_thm)) thm2;
          val thm4 = CONV_RULE (RAND_CONV (SIMP_CONV (arith_ss) [LET_DEF])) thm3;

        in
          thm4
        end
    end;

(*

  bir_exec_prog_step_n var_eq_thm thm

  val (os, steps, state2) = (dest_triple o snd o dest_eq o concl) thm;
*)

end
