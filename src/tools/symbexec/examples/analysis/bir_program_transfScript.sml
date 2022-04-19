
open HolKernel Parse boolLib bossLib;

open pred_setTheory;

  open bir_programTheory;
  open bir_inst_liftingTheory;

open HolBACoreSimps;

  val bir_state_ss = rewrites (type_rws ``:bir_state_t``);

val _ = new_theory "bir_program_transf";


val bir_exec_stmtB_INIT_FINAL_Running_thm = store_thm(
   "bir_exec_stmtB_INIT_FINAL_Running_thm", ``
!stmt bs bs'.
  (SND (bir_exec_stmtB stmt bs) = bs') ==>
  (bs.bst_status = BST_Running) ==>
  (bs'.bst_status = BST_Running \/ (bs.bst_pc = bs'.bst_pc))
``,
  REPEAT GEN_TAC >>
  DISCH_TAC >>

  Cases_on `stmt` >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtB_def, bir_exec_stmt_assign_def] >>
    Cases_on `bir_eval_exp b0 bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
    Cases_on `bir_env_write b x bs.bst_environ` >> (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    )
  ) >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtB_def, bir_exec_stmt_assert_def] >>
    Cases_on `bir_eval_exp b bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
    Cases_on `bir_dest_bool_val x` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    Cases_on `x'` >> (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    )
  ) >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtB_def, bir_exec_stmt_assume_def] >>
    Cases_on `bir_eval_exp b bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
    Cases_on `bir_dest_bool_val x` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    Cases_on `x'` >> (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    )
  ) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtB_def, bir_exec_stmt_observe_def] >>
  Q.ABBREV_TAC `A = MAP (\e. bir_eval_exp e bs.bst_environ) l` >>
  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [LET_DEF] >>

  Cases_on `bir_eval_exp b bs.bst_environ` >- (
    ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
  Cases_on `bir_dest_bool_val x` >- (
    ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
  Cases_on `x'` >> Cases_on `EXISTS IS_NONE A` >> (
    ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  )
);


val bir_exec_stmt_jmp_to_label_INIT_FINAL_Running_thm = store_thm(
   "bir_exec_stmt_jmp_to_label_INIT_FINAL_Running_thm", ``
!p l bs bs'.
  (bir_exec_stmt_jmp_to_label p l bs = bs') ==>
  (bs.bst_status = BST_Running) ==>
  (bs'.bst_status = BST_Running \/ (bs.bst_pc = bs'.bst_pc))
``,
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmt_jmp_to_label_def] >>
  Cases_on `MEM l (bir_labels_of_program p)` >- (
    ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
  ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
);


val bir_exec_stmt_jmp_INIT_FINAL_Running_thm = store_thm(
   "bir_exec_stmt_jmp_INIT_FINAL_Running_thm", ``
!p le bs bs'.
  (bir_exec_stmt_jmp p le bs = bs') ==>
  (bs.bst_status = BST_Running) ==>
  (bs'.bst_status = BST_Running \/ (bs.bst_pc = bs'.bst_pc))
``,
  REPEAT GEN_TAC >>
  DISCH_TAC >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
    Cases_on `bir_eval_label_exp le bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
      METIS_TAC [bir_status_t_distinct]
    ) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
    METIS_TAC [bir_exec_stmt_jmp_to_label_INIT_FINAL_Running_thm]
);

val bir_exec_stmtE_INIT_FINAL_Running_thm = store_thm(
   "bir_exec_stmtE_INIT_FINAL_Running_thm", ``
!p estmt bs bs'.
  (bir_exec_stmtE p estmt bs = bs') ==>
  (bs.bst_status = BST_Running) ==>
  ((bs.bst_pc <> bs'.bst_pc) ==> (bs'.bst_status = BST_Running))
``,
  REPEAT GEN_TAC >>
  DISCH_TAC >>

  Cases_on `estmt` >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtE_def] >>
    METIS_TAC [bir_exec_stmt_jmp_INIT_FINAL_Running_thm]
  ) >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
    Cases_on `bir_eval_exp b bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [LET_DEF] >>
    Cases_on `bir_dest_bool_val x` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
    ) >>

    Cases_on `x'` >> (
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
      METIS_TAC [bir_exec_stmt_jmp_INIT_FINAL_Running_thm]
    )
  ) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_halt_def] >>
  Cases_on `bir_eval_exp b bs.bst_environ` >- (
      ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
      ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF] >>
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
  ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF] >>
  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
);


val bir_exec_step_INIT_FINAL_Running_thm = store_thm(
   "bir_exec_step_INIT_FINAL_Running_thm", ``
!p bs bs'.
  (SND (bir_exec_step p bs) = bs') ==>
  (((bs.bst_pc <> bs'.bst_pc) ==> (bs'.bst_status = BST_Running)) /\
   ((bs'.bst_status = BST_Running) ==> (bs.bst_status = BST_Running)))
``,
  REPEAT GEN_TAC >>
  DISCH_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_def] >>
  Cases_on `bir_state_is_terminated bs` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `bir_get_current_statement p bs.bst_pc` >- (
    ASSUME_TAC (Q.SPEC `bs` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_failed_def, bir_state_is_terminated_def] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `x` >- (
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmt_def] >>
    Cases_on `bir_exec_stmtB b bs` >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [LET_DEF] >>

    Cases_on `bir_state_is_terminated r` >- (
      FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_failed_def, bir_state_is_terminated_def] >>
      METIS_TAC [bir_exec_stmtB_INIT_FINAL_Running_thm, pairTheory.SND]
    ) >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_state_set_failed_def, bir_state_is_terminated_def] >>
    ASSUME_TAC (Q.SPEC `r` bir_state_t_literal_nchotomy) >>
    ASSUME_TAC (Q.SPEC `bs'` bir_state_t_literal_nchotomy) >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [] >>
    FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) []
  ) >>

  FULL_SIMP_TAC (std_ss++bir_state_ss++holBACore_ss) [bir_exec_stmt_def, bir_state_is_terminated_def] >>
  IMP_RES_TAC bir_exec_stmtE_INIT_FINAL_Running_thm
);

val bir_exec_step_state_PC_DIFF_IMP_FINAL_Running_thm = store_thm(
   "bir_exec_step_state_PC_DIFF_IMP_FINAL_Running_thm", ``
!bprog bs bs'.
  (bir_exec_step_state bprog bs = bs') ==>
  (bs.bst_pc <> bs'.bst_pc) ==>
  (bs'.bst_status = BST_Running)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_state_def] >>
  IMP_RES_TAC bir_exec_step_INIT_FINAL_Running_thm
);

val bir_exec_step_state_FINAL_Running_IMP_INITIAL_Running_thm = store_thm(
   "bir_exec_step_state_FINAL_Running_IMP_INITIAL_Running_thm", ``
!bprog bs bs'.
  (bir_exec_step_state bprog bs = bs') ==>
  (bs'.bst_status = BST_Running) ==>
  (bs.bst_status = BST_Running)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_state_def] >>
  IMP_RES_TAC bir_exec_step_INIT_FINAL_Running_thm
);


(*
val _thm = store_thm(
   "_thm", ``
!.
  (bir_exec_steps_GEN (cfst, pcls) p st (SOME n) = BER_Ended lo i n' bs') ==>
  (bs'.bst_status = BST_Running) ==>
  ()
``,
  cheat
);
*)

(*
listTheory.REVERSE_GENLIST

val GENLISTREV_def = Define `
    GENLISTREV f n = 
`;

listTheory.GENLIST


val _thm = store_thm(
   "_thm", ``
!p st n.
  (GENLIST (\x. f (SUC x)) n)
``,
  cheat
);
*)

val GENLIST_FUN_SUC_EQ_thm = store_thm(
   "GENLIST_FUN_SUC_EQ_thm", ``
!f g n.
  (!m. (m <= n) ==> (f m = g m)) ==>
  (GENLIST f (SUC n) =
   GENLIST g (SUC n))
``,
  Induct_on `n` >> (
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) []
  ) >>

  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x y. A`` (ASSUME_TAC o Q.SPECL [`f`, `g`]) >>

  `!m. m <= n ==> f m = g m` by (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPEC `m`) >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC std_ss [listTheory.GENLIST]
);

val GENLIST_FUN_SUC_SUB_EQ_thm = store_thm(
   "GENLIST_FUN_SUC_SUB_EQ_thm", ``
!f n.
  GENLIST (\m. f (SUC (n - m))) (SUC n) =
  GENLIST (\m. f (SUC  n - m )) (SUC n)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC GENLIST_FUN_SUC_EQ_thm >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [arithmeticTheory.SUB_LEFT_SUC] >>

  Cases_on `m = n` >- (
    FULL_SIMP_TAC std_ss [arithmeticTheory.SUC_SUB]
  ) >>

  FULL_SIMP_TAC arith_ss []
);

val bir_exec_infinite_steps_fun_COMM_thm = store_thm(
   "bir_exec_infinite_steps_fun_COMM_thm", ``
!p st n.
  (bir_exec_infinite_steps_fun p (bir_exec_step_state p st) n = bir_exec_step_state p (bir_exec_infinite_steps_fun p st n))
``,
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>

  METIS_TAC [arithmeticTheory.FUNPOW, arithmeticTheory.FUNPOW_SUC]
);

val bir_exec_infinite_steps_fun_COUNT_PCs_SUC_MAP_ALT_thm = store_thm(
   "bir_exec_infinite_steps_fun_COUNT_PCs_SUC_MAP_ALT_thm", ``
!pc_cond bprog bs n.
  (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs (SUC n) =
   SUM (MAP (\x. if bir_state_COUNT_PC pc_cond x then 1 else 0) (REVERSE (GENLIST (\y. bir_exec_infinite_steps_fun bprog bs (SUC y)) (SUC n)))))
``,
  Induct_on `n` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_DEF] >>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [] >>
    SIMP_TAC std_ss [REWRITE_CONV [arithmeticTheory.ONE, bir_exec_infinite_steps_fun_REWRS] ``bir_exec_infinite_steps_fun bprog' bs 1``]
  ) >>

  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [Once bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
  ASM_SIMP_TAC pure_ss [] >>
  REWRITE_TAC [listTheory.REVERSE_GENLIST] >>
  POP_ASSUM (K ALL_TAC) >>

  REWRITE_TAC [GSYM (CONJUNCT2 bir_exec_infinite_steps_fun_REWRS)] >>

  CONV_TAC (RAND_CONV (SIMP_CONV (pure_ss) [Once listTheory.GENLIST])) >>
  SIMP_TAC std_ss [listTheory.MAP_SNOC, listTheory.SUM_SNOC] >>
  SIMP_TAC std_ss [REWRITE_CONV [arithmeticTheory.ONE, bir_exec_infinite_steps_fun_REWRS] ``bir_exec_infinite_steps_fun bprog' bs 1``] >>

  SIMP_TAC std_ss [
   prove(
    ``GENLIST (\m.  bir_exec_infinite_steps_fun bprog' bs (SUC (SUC (n - m)))) (SUC n) =
      GENLIST (\m.  bir_exec_infinite_steps_fun bprog' bs (SUC (SUC  n - m ))) (SUC n)``,
    FULL_SIMP_TAC std_ss [GENLIST_FUN_SUC_SUB_EQ_thm]
   )]>>

  CASE_TAC >> (
    FULL_SIMP_TAC std_ss [LET_DEF, arithmeticTheory.ADD1]
  )
);

val bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def = Define `
   (bir_exec_infinite_steps_fun_COUNT_PCs_ALT pc_cond bprog bs 0 = 0) /\
   (bir_exec_infinite_steps_fun_COUNT_PCs_ALT pc_cond bprog bs (SUC n) = 
    let
      r = bir_exec_infinite_steps_fun_COUNT_PCs_ALT pc_cond bprog bs n
    in
      if bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun bprog bs (SUC n)) then
        SUC r
      else
        r)
`;

val bir_exec_infinite_steps_fun_COUNT_PCs_ALT_thm = store_thm(
   "bir_exec_infinite_steps_fun_COUNT_PCs_ALT_thm", ``
  bir_exec_infinite_steps_fun_COUNT_PCs =
  bir_exec_infinite_steps_fun_COUNT_PCs_ALT
``,
  REPEAT (MATCH_MP_TAC boolTheory.EQ_EXT >> GEN_TAC) >>
  rename1 `bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p bs n` >>

  Cases_on `n` >- (
    REWRITE_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def, bir_exec_infinite_steps_fun_COUNT_PCs_def]
  ) >>

  REWRITE_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_SUC_MAP_ALT_thm] >>
  REWRITE_TAC [rich_listTheory.MAP_REVERSE, rich_listTheory.SUM_REVERSE] >>
  REWRITE_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def] >>

  Induct_on `n'` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def, LET_DEF] >>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def]
  ) >>

  SIMP_TAC (pure_ss) [Once listTheory.GENLIST] >>
  SIMP_TAC pure_ss [listTheory.MAP_SNOC, listTheory.SUM_SNOC] >>
  ASM_SIMP_TAC pure_ss [] >>

  SIMP_TAC std_ss [GSYM bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def] >>
  POP_ASSUM (K ALL_TAC) >>
  CONV_TAC (RAND_CONV (SIMP_CONV (pure_ss) [Once bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def])) >>

  CASE_TAC >> (
    FULL_SIMP_TAC std_ss [LET_DEF, arithmeticTheory.ADD1]
  )
);

val bir_exec_infinite_steps_fun_COUNT_PCs_LAST_STEP_thm = store_thm(
   "bir_exec_infinite_steps_fun_COUNT_PCs_LAST_STEP_thm", ``
!pc_cond bprog bs n.
  (bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun bprog bs (SUC n))) ==>
  (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs (SUC n) =
   SUC (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs n))
``,
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_thm, bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def, LET_DEF]
);

val bir_exec_infinite_steps_fun_COUNT_PCs_GROWS_thm = store_thm(
   "bir_exec_infinite_steps_fun_COUNT_PCs_GROWS_thm", ``
!pc_cond bprog bs n n'.
    (n' < n) ==>
    (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs n' <= bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs n)
``,
  Induct_on `n` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `n' = n` >- (
    FULL_SIMP_TAC (std_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_thm] >>
    FULL_SIMP_TAC (std_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def, LET_DEF] >>
    Cases_on `bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun bprog bs (SUC n))` >> (
      FULL_SIMP_TAC arith_ss []
    )
  ) >>
  `n' < n` by (
    FULL_SIMP_TAC arith_ss []
  ) >>

  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`pc_cond`, `bprog`, `bs`, `n'`]) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC (std_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_thm] >>
  FULL_SIMP_TAC (std_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_ALT_def, LET_DEF] >>

  Cases_on `bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun bprog bs (SUC n))` >> (
    FULL_SIMP_TAC arith_ss []
  )
);


val bir_exec_infinite_steps_fun_COUNT_PCs_LESS_STEPS_IMP_thm = store_thm(
   "bir_exec_infinite_steps_fun_COUNT_PCs_LESS_STEPS_IMP_thm", ``
!pc_cond bprog bs n k.
  (bir_state_COUNT_PC pc_cond (bir_exec_infinite_steps_fun bprog bs n)) ==>
  (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs n = k) ==>
  (!n'.
    (n' < n) ==>
    (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond bprog bs n' < k))
``,
  REPEAT STRIP_TAC >>

  Cases_on `n` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>

  IMP_RES_TAC bir_exec_infinite_steps_fun_COUNT_PCs_LAST_STEP_thm >>
  FULL_SIMP_TAC std_ss [] >>

  PAT_X_ASSUM ``bir_state_COUNT_PC A B`` (K ALL_TAC) >>
  PAT_X_ASSUM ``SUC A = B`` (fn thm => REWRITE_TAC [GSYM thm]) >>

  Cases_on `n' = n''` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  `n' < n''` by (
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC std_ss [GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
  METIS_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_GROWS_thm]
);

val bir_exec_step_state_PC_DIFF_IMP_Running_thm = store_thm(
   "bir_exec_step_state_PC_DIFF_IMP_Running_thm", ``
!bprog bs bs'.
  (bir_exec_step_state bprog bs = bs') ==>
  (bs.bst_pc <> bs'.bst_pc) ==>
  (bs.bst_status = BST_Running /\ bs'.bst_status = BST_Running)
``,
  METIS_TAC [bir_exec_step_state_PC_DIFF_IMP_FINAL_Running_thm, bir_exec_step_state_FINAL_Running_IMP_INITIAL_Running_thm]
);

val bir_exec_infinite_steps_fun_NOT_terminated_thm = store_thm(
   "bir_exec_infinite_steps_fun_NOT_terminated_thm", ``
!bprog bs n L bs'.
  (bir_exec_infinite_steps_fun bprog bs n = bs') ==>
  (~(bir_state_is_terminated bs')) ==>
  (!n'.
    (n' < n) ==>
    (~(bir_state_is_terminated (bir_exec_infinite_steps_fun bprog bs n'))))
``,
  Induct_on `n` >> (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
  ) >>

  FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`bprog`, `bir_exec_step_state bprog bs`]) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  Cases_on `n' = n` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COMM_thm] >>
    METIS_TAC [bir_exec_step_state_FINAL_Running_IMP_INITIAL_Running_thm]
  ) >>

  `n' < n` by (
    FULL_SIMP_TAC arith_ss []
  ) >>

  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COMM_thm] >>
  METIS_TAC [bir_exec_step_state_FINAL_Running_IMP_INITIAL_Running_thm]
);

val bir_exec_infinite_steps_fun_LAST_PC_DIFF_IMP_Running_thm = store_thm(
   "bir_exec_infinite_steps_fun_LAST_PC_DIFF_IMP_Running_thm", ``
!bprog bs k bs'.
  (bir_exec_infinite_steps_fun bprog bs (SUC k) = bs') ==>
  ((bir_exec_infinite_steps_fun bprog bs k).bst_pc <> bs'.bst_pc) ==>
  (bs.bst_status = BST_Running /\ bs'.bst_status = BST_Running)
``,
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COMM_thm] >>

  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  IMP_RES_TAC (SIMP_RULE std_ss [] bir_exec_step_state_PC_DIFF_IMP_Running_thm) >>
  ASM_REWRITE_TAC [] >>

  IMP_RES_TAC (SIMP_RULE std_ss [bir_state_is_terminated_def] bir_exec_infinite_steps_fun_NOT_terminated_thm) >>

  Cases_on `k` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
  ) >>

  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `0`) >>
  FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_REWRS]
);

val bir_exec_infinite_steps_fun_PC_DIFF_IMP_Running_thm = store_thm(
   "bir_exec_infinite_steps_fun_PC_DIFF_IMP_Running_thm", ``
!bprog bs n bs' L.
  (bir_exec_infinite_steps_fun bprog bs n = bs') ==>
  (n > 0) ==>
  (!n'. n' < n ==> (bir_exec_infinite_steps_fun bprog bs n').bst_pc IN L) ==>
  (bs'.bst_pc NOTIN L) ==>
  (bs.bst_status = BST_Running /\ bs'.bst_status = BST_Running)
``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  Cases_on `n` >> (
    FULL_SIMP_TAC arith_ss []
  ) >>

  `(bir_exec_infinite_steps_fun bprog bs n').bst_pc <> bs'.bst_pc` by (
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `n'`) >>
    FULL_SIMP_TAC arith_ss [] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [IN_APP]
  ) >>
  IMP_RES_TAC bir_exec_infinite_steps_fun_LAST_PC_DIFF_IMP_Running_thm >>
  ASM_REWRITE_TAC []
);

val bir_exec_infinite_steps_fun_IMP_fun_COUNT_PCs_thm = store_thm(
   "bir_exec_infinite_steps_fun_IMP_fun_COUNT_PCs_thm", ``
!bprog bs n L bs' Lf.
  (bir_exec_infinite_steps_fun bprog bs n = bs') ==>
  (n > 0) ==>
  (bs'.bst_pc IN Lf) ==>
  (L INTER Lf = EMPTY) ==>
  (!n'.
    (n' < n) ==>
    ((bir_exec_infinite_steps_fun bprog bs n').bst_pc IN L)) ==>
  (bir_exec_infinite_steps_fun_COUNT_PCs (F, Lf) bprog bs n = 1)
``,
  Cases_on `n` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``SUC n' > 0`` (K ALL_TAC) >>
  REPEAT (POP_ASSUM MP_TAC) >>
  Q.ID_SPEC_TAC `bs'` >>
  Q.ID_SPEC_TAC `L` >>
  Q.ID_SPEC_TAC `n'` >>
  Q.ID_SPEC_TAC `bs` >>

  Induct_on `n'` >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>

    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `0`) >>
    FULL_SIMP_TAC arith_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>

    `bs.bst_status = BST_Running /\
     bs'.bst_status = BST_Running` by (
      `bs.bst_pc <> bs'.bst_pc` by (
        REPEAT STRIP_TAC >>
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM DISJOINT_DEF, IN_DISJOINT] >>
        METIS_TAC []
      ) >>
      IMP_RES_TAC bir_exec_step_state_PC_DIFF_IMP_Running_thm >>
      ASM_SIMP_TAC std_ss []
    ) >>

    FULL_SIMP_TAC pure_ss [arithmeticTheory.ONE, bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_state_COUNT_PC_def, pred_setTheory.IN_APP]
  ) >>

  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `k = SUC n'` >>

  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
  FULL_SIMP_TAC pure_ss [bir_exec_infinite_steps_fun_COUNT_PCs_def] >>

(*
  FULL_SIMP_TAC pure_ss [bir_exec_infinite_steps_fun_COMM_thm] >>
*)
  Q.ABBREV_TAC `bs'' = bir_exec_step_state bprog bs` >>
  PAT_X_ASSUM ``!x y.A`` (ASSUME_TAC o Q.SPECL [`bs''`, `L`]) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  `!n'. n' < k ==> (bir_exec_infinite_steps_fun bprog bs'' n').bst_pc IN L` by (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `SUC n''`) >>
    REV_FULL_SIMP_TAC arith_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
    METIS_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>

  `bs''.bst_pc IN L` by (
    Q.UNABBREV_TAC `k` >>
    Q.UNABBREV_TAC `bs''` >>
    REPEAT (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `1`)) >>
    FULL_SIMP_TAC pure_ss [arithmeticTheory.ONE, bir_exec_infinite_steps_fun_REWRS, bir_exec_infinite_steps_fun_COMM_thm] >>
    FULL_SIMP_TAC arith_ss []
  ) >>

  `bs''.bst_pc <> bs'.bst_pc` by (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM DISJOINT_DEF, IN_DISJOINT] >>
    METIS_TAC []
  ) >>

  `k > 0` by (
    Cases_on `k = 0` >- (
      FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
      REV_FULL_SIMP_TAC std_ss []
    ) >>
    FULL_SIMP_TAC arith_ss []
  ) >>

  `bs'.bst_pc NOTIN L /\
   bs''.bst_pc NOTIN Lf` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM DISJOINT_DEF, IN_DISJOINT] >>
    METIS_TAC []
  ) >>

  IMP_RES_TAC bir_exec_infinite_steps_fun_PC_DIFF_IMP_Running_thm >>

  FULL_SIMP_TAC pure_ss [arithmeticTheory.ONE, bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_state_COUNT_PC_def, pred_setTheory.IN_APP]
);

val bir_exec_infinite_steps_fun_IMP_COUNT_STEPS_thm = store_thm(
   "bir_exec_infinite_steps_fun_IMP_COUNT_STEPS_thm", ``
!bprog bs n L bs' Lf.

  (bir_exec_infinite_steps_fun bprog bs n = bs') ==>
  (n > 0) ==>

  (bs'.bst_pc IN Lf) ==>
  (L INTER Lf = EMPTY) ==>

  (!n'.
    (n' < n) ==>
    ((bir_exec_infinite_steps_fun bprog bs n').bst_pc IN L)) ==>

(*
(bs'.bst_pc.bpc_label IN ls) ==>
(* TODO: need to add some more assumptions about ls in order to generalize this a bit *)
*)

  (bir_exec_infinite_steps_COUNT_STEPS (F, Lf) (SOME 1) bprog bs = SOME n)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_exec_infinite_steps_fun_IMP_fun_COUNT_PCs_thm >>

  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def] >>
  REWRITE_TAC [whileTheory.OLEAST_EQ_SOME] >>
  ASM_SIMP_TAC std_ss [] >>

  `bs'.bst_pc NOTIN L` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM DISJOINT_DEF, IN_DISJOINT] >>
    METIS_TAC []
  ) >>
  IMP_RES_TAC bir_exec_infinite_steps_fun_PC_DIFF_IMP_Running_thm >>

  REPEAT STRIP_TAC >- (
    `~(bir_state_is_terminated bs')` by (
      ASM_SIMP_TAC std_ss [bir_state_is_terminated_def]
    ) >>
    METIS_TAC [bir_exec_infinite_steps_fun_NOT_terminated_thm]
  ) >>

  `bir_state_COUNT_PC (F, Lf) (bir_exec_infinite_steps_fun bprog bs n)` by (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_state_COUNT_PC_def, IN_SING, SING_applied, IN_APP]
  ) >>

  IMP_RES_TAC bir_exec_infinite_steps_fun_COUNT_PCs_LESS_STEPS_IMP_thm >>
  FULL_SIMP_TAC arith_ss []
);


val bir_exec_infinite_steps_fun_IMP_exec_to_labels_thm = store_thm(
   "bir_exec_infinite_steps_fun_IMP_exec_to_labels_thm", ``
!bprog bs n L bs' Lf.

  (bir_exec_infinite_steps_fun bprog bs n = bs') ==>
  (n > 0) ==>

  (bs'.bst_pc IN Lf) ==>
  (L INTER Lf = EMPTY) ==>

  (!n'.
    (n' < n) ==>
    ((bir_exec_infinite_steps_fun bprog bs n').bst_pc IN L)) ==>

  (!pcl. pcl IN Lf ==> pcl.bpc_index = 0) ==>

  ?lo.
  (bir_exec_to_labels (IMAGE (\x. x.bpc_label) Lf) bprog bs = BER_Ended lo n 1 bs')
``,
  REWRITE_TAC
    [bir_exec_to_labels_n_def, bir_exec_to_labels_def, bir_exec_steps_GEN_def] >>
  REPEAT STRIP_TAC >>

  `(\pc. pc.bpc_index = 0 /\ pc.bpc_label IN (IMAGE (\x. x.bpc_label) Lf)) = Lf` by (
    FULL_SIMP_TAC std_ss [EXTENSION, IN_SING, IN_APP] >>
    REPEAT STRIP_TAC >>
    EQ_TAC >- (
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setSimps.PRED_SET_ss) [] >>
      `x = x'` by (
        Cases_on `x` >> Cases_on `x'` >>
        FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setSimps.PRED_SET_ss) [IN_APP] >>
        METIS_TAC [bir_programcounter_t_bpc_index]
      ) >>
      METIS_TAC [IN_APP]
    ) >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setSimps.PRED_SET_ss) [] >>

    METIS_TAC [IN_APP]
  ) >>
  ASM_SIMP_TAC std_ss [] >>

  IMP_RES_TAC bir_exec_infinite_steps_fun_IMP_COUNT_STEPS_thm >>
  IMP_RES_TAC bir_exec_infinite_steps_fun_IMP_fun_COUNT_PCs_thm >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
);




(*
val bir_exec_to_labels_IMP_thm = store_thm(
   "bir_exec_to_labels_IMP_thm", ``
!L bprog bs lo n bs'.
(bir_exec_to_labels L bprog bs = BER_Ended lo n 1 bs') ==>
(!l. l IN L ==> IS_BL_Address l) ==>
  ?n'.
  (bir_exec_to_addr_label_n bprog bs n' = BER_Ended lo n n' bs')
``,
  REWRITE_TAC
    [bir_exec_to_labels_n_def, bir_exec_to_labels_def, bir_exec_to_addr_label_n_def, bir_exec_steps_GEN_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [LET_DEF] >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS
              (F,(\pc. pc.bpc_index = 0 /\ pc.bpc_label IN L)) (SOME 1) bprog
              bs` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  cheat
  (* TODO: this theorem might be not so useful because of the IS_BL_Address assumption *)
);
*)

local
  open symb_recordTheory;
in

val bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm0 = store_thm(
   "bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm0", ``
!bprog bs n L bs'.
  (step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  (n > 0)
``,
  FULL_SIMP_TAC std_ss [step_n_in_L_def, step_n_in_L_relaxed_def]
);

val bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm1 = store_thm(
   "bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm1", ``
!bprog bs n L bs'.
  (step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  (bir_exec_infinite_steps_fun bprog bs n = bs')
``,
  FULL_SIMP_TAC std_ss [step_n_in_L_def, step_n_in_L_relaxed_def, bir_programTheory.bir_exec_infinite_steps_fun_def, step_n_def]
);

val bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm2 = store_thm(
   "bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm2", ``
!bprog bs n L bs'.
  (step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  (!n'.
    (n' < n) ==>
    ((bir_exec_infinite_steps_fun bprog bs n').bst_pc IN L))
``,
  FULL_SIMP_TAC std_ss [step_n_in_L_def, step_n_in_L_relaxed_def, bir_programTheory.bir_exec_infinite_steps_fun_def, step_n_def] >>

  REPEAT STRIP_TAC >>
  Cases_on `n' = 0` >- (
    FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_0]
  ) >>

  `0 < n'` by (
    FULL_SIMP_TAC arith_ss []
  ) >>
  METIS_TAC []
);

val bir_step_n_in_L_IMP_exec_to_labels_thm = store_thm(
   "bir_step_n_in_L_IMP_exec_to_labels_thm", ``
!bprog bs n L bs' Lf.

(step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>

(bs'.bst_pc IN Lf) ==>
(L INTER Lf = EMPTY) ==>

(!pcl. pcl IN Lf ==> pcl.bpc_index = 0) ==>

  ?lo.
  (bir_exec_to_labels (IMAGE (\x. x.bpc_label) Lf) bprog bs = BER_Ended lo n 1 bs')
``,
  REPEAT STRIP_TAC >>

  IMP_RES_TAC bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm0 >>
  IMP_RES_TAC bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm1 >>
  IMP_RES_TAC bir_step_n_in_L_IMP_exec_infinite_steps_fun_thm2 >>

  IMP_RES_TAC bir_exec_infinite_steps_fun_IMP_exec_to_labels_thm >>

  METIS_TAC []
);

val bir_step_n_in_L_IMP_exec_to_labels_SING_thm = store_thm(
   "bir_step_n_in_L_IMP_exec_to_labels_SING_thm", ``
!bprog bs n L bs'.

(step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>

((bs'.bst_pc) NOTIN L) ==>
(bs'.bst_pc.bpc_index = 0) ==>

  ?lo.
  (bir_exec_to_labels {bs'.bst_pc.bpc_label} bprog bs = BER_Ended lo n 1 bs')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ((GSYM o EVAL) ``(IMAGE (\x. x.bpc_label) {bs'.bst_pc})``) >>
  REV_FULL_SIMP_TAC pure_ss [] >>
  POP_ASSUM (K ALL_TAC) >>
  Q.ABBREV_TAC `Lf = {bs'.bst_pc}` >>

  `bs'.bst_pc IN Lf` by (
    METIS_TAC [IN_SING]
  ) >>
  `L INTER Lf = EMPTY` by (
    METIS_TAC [GSYM DISJOINT_DEF, IN_DISJOINT, IN_SING]
  ) >>
  `!pcl. pcl IN Lf ==> pcl.bpc_index = 0` by (
    METIS_TAC [IN_SING]
  ) >>

  IMP_RES_TAC bir_step_n_in_L_IMP_exec_to_labels_thm >>
  METIS_TAC []
);


end;

(* ........................... *)

val bir_step_n_in_L_jgmt_def = Define `
    bir_step_n_in_L_jgmt bprog l L pre post =
 !st.
   (st.bst_pc = l) ==>
   (pre st) ==>
   (?n st'.
     (step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) st n L st') /\
     (post st st'))
`;

val abstract_jgmt_rel_def = Define `
    abstract_jgmt_rel m (l:'a) (ls:'a->bool) pre post =
  !ms .
   ((m.pc ms) = l) ==> (pre ms) ==>
   ?ms'. ((m.weak ms ls ms') /\
    (post ms ms'))
`;


val bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm = prove (``
!bprog l L ls pre post.
(bir_step_n_in_L_jgmt
  bprog
  (bir_block_pc l)
  L
  pre
  post) ==>

(!st. pre st ==> st.bst_pc.bpc_index = 0) ==>
(L INTER (IMAGE bir_block_pc ls) = EMPTY) ==>
(!st st'. post st st' ==> st'.bst_pc IN (IMAGE bir_block_pc ls)) ==>
(!st st'. post st st' ==> (~bir_state_is_terminated st')) ==>

(abstract_jgmt_rel
  (bir_etl_wm bprog)
  l
  ls
  pre
  post)
``,

  REWRITE_TAC [bir_step_n_in_L_jgmt_def] >>
  REPEAT STRIP_TAC >>

  REWRITE_TAC [abstract_jgmt_rel_def] >>
  SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS) [bir_wm_instTheory.bir_etl_wm_def] >>
  SIMP_TAC std_ss [bir_wm_instTheory.bir_weak_trs_def] >>

  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x. A ==> B ==> C`` (ASSUME_TAC o Q.SPEC `ms`) >>
  PAT_X_ASSUM ``!x. A ==> B = C`` (ASSUME_TAC o Q.SPEC `ms`) >>
  PAT_X_ASSUM ``!x y. A ==> B`` (ASSUME_TAC o Q.SPEC `ms`) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  `ms.bst_pc = bir_block_pc l` by (
    Cases_on `ms.bst_pc` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_block_pc_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_programcounter_t_component_equality]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `st'.bst_pc IN (IMAGE bir_block_pc ls)` by (
    METIS_TAC []
  ) >>

  `!pcl. pcl IN (IMAGE bir_block_pc ls) ==> pcl.bpc_index = 0` by (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_IMAGE, bir_programTheory.bir_block_pc_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `pcl` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_programcounter_t_component_equality]
  ) >>

  IMP_RES_TAC bir_step_n_in_L_IMP_exec_to_labels_thm >>

  `IMAGE (\x. x.bpc_label) (IMAGE bir_block_pc ls) = ls` by (
    REWRITE_TAC [EXTENSION] >>
    REPEAT STRIP_TAC >>
    EQ_TAC >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_IMAGE, bir_programTheory.bir_block_pc_def] >>
      REPEAT STRIP_TAC >>
      Cases_on `x''` >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_programcounter_t_component_equality]
    ) >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_IMAGE, bir_programTheory.bir_block_pc_def] >>
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `<|bpc_label := x; bpc_index := 0|>` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_IMAGE, bir_programTheory.bir_block_pc_def]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
);




(*
TODO: go to didrik style m0_mod weak transition relation
*)

val m_weak_trs_def = Define `
    m_weak_trs pcf stepf ms ls ms' = 
        ?n.
          ((n > 0) /\
           (FUNPOW_OPT stepf n ms = SOME ms') /\
           ((pcf ms') IN ls)
          ) /\
          !n'.
            (((n' < n) /\ (n' > 0)) ==>
            ?ms''.
              (FUNPOW_OPT stepf n' ms = SOME ms'') /\
              ((pcf ms'') NOTIN ls)
            )`;
val m_weak_model_def = Define `
    m_weak_model pcf bmr  = <|
    trs  := bmr.bmr_step_fun;
    weak := m_weak_trs pcf bmr.bmr_step_fun;
    pc   := pcf
  |>`;
val m0_mod_weak_trs_def = Define `
    m0_mod_weak_trs = m_weak_trs (\x. x.base.REG RName_PC) (m0_mod_bmr (T,T)).bmr_step_fun
`;
val m0_mod_weak_model_def = Define `
    m0_mod_weak_model = m_weak_model (\x. x.base.REG RName_PC) (m0_mod_bmr (T,T))
`;
val m0_weak_model_def = Define `
    m0_weak_model = m_weak_model (\x. x.REG RName_PC) (m0_bmr (T,T))
`;

val m_triple_rel_def = Define `
    m_triple_rel wm bmr mms l ls pre post =
    abstract_jgmt_rel wm l ls
      (\ms. (bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains bmr ms) mms) /\
            (pre ms))         
      (\ms ms'. (bmr.bmr_extra ms')  /\
            (EVERY (bmr_ms_mem_contains bmr ms') mms) /\
            (post ms ms'))
`;
val m0_mod_triple_rel_def = Define `
    m0_mod_triple_rel = m_triple_rel m0_mod_weak_model (m0_mod_bmr (T,T))
`;

(* TODO: translate to pure Cortex-M0 property *)
(* =================================================================================== *)
(*
bir_backlifterTheory.bir_post_bir_to_arm8_def
lift_contract_thm
src/tools/backlifter/bir_backlifterLib.sml

get_arm8_contract_sing

examples/tutorial/7-composition/tutorial_backliftingScript.sml
*)
(* =================================================================================== *)

(* TODO: stolen and adjusted/generalized from "bir_backlifterTheory.bir_is_lifted_prog_MULTI_STEP_EXEC_compute" *)
(* =================================================================================== *)
val bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm =
  prove(
  ``!mu bs bs' ms mla (p:'a bir_program_t) (r:('c, 'd, 'b) bir_lifting_machine_rec_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog r mu mms p ==>
    bmr_rel r bs ms ==>
    MEM (BL_Address mla) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains r ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
    ?ms' li.
    (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
    bmr_ms_mem_unchanged r ms ms' mu /\
    EVERY (bmr_ms_mem_contains r ms') mms /\
    (bs'.bst_pc = bir_block_pc (BL_Address li)) /\
    MEM (BL_Address li) (bir_labels_of_program p) /\
    bmr_rel r bs' ms'
``,

REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:('c, 'd, 'b) bir_lifting_machine_rec_t``, ``mu:'c word_interval_t``,
                    ``mms:(('c word)# ('d word) list) list``,
                    ``p:'a bir_program_t``] bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
bir_auxiliaryLib.QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_state_is_terminated_def]
);

val bir_is_lifted_prog_MULTI_STEP_EXEC_compute_32_8_thm =
  INST_TYPE
    [Type.gamma |-> ``:32``, Type.delta |-> ``:8``]
    bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm;
(* =================================================================================== *)


(*

TODO: this is probably in precondition lifting
"bir_backlifterTheory.exist_bir_of_arm8_thm"
bir_backlifterTheory.bir_pre_arm8_to_bir_def
bir_backlifterTheory.bir_post_bir_to_arm8_def
((
!ms.
?bs.
  (bir_envty_list_b birenvtyl st.bst_environ) /\
  bmr_rel (m0_mod_bmr (T,T)) bs ms
))
bir_lifting_machinesTheory.m0_mod_bmr_def



((
``
!bprog bs n L bs'.
(step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  ?n' lo.
  (bir_exec_to_addr_label_n bprog bs n' = BER_Ended lo n n' bs')
``
))
*)

val backlift_contract_GEN_thm = store_thm(
   "backlift_contract_GEN_thm", ``
!wm_a wm R_a pcaf pre extra_ms R_a_impl pre_a post_a post l ls.
  (!ms. pre ms ==> extra_ms ms) ==>

  (!ms. extra_ms ms ==> ?ms_a. (R_a ms ms_a /\ R_a_impl ms ms_a)) ==>
  (!ms ms_a. R_a_impl ms ms_a ==> R_a ms ms_a ==> wm_a.pc ms_a = pcaf (wm.pc ms)) ==>
  (!ms ms_a. R_a ms ms_a ==> pre ms ==> pre_a ms_a) ==>

  (!ms ms_a ms_a' ls. pre ms ==> pre_a ms_a ==> post_a ms_a ms_a' ==> R_a ms ms_a ==> wm_a.weak ms_a (IMAGE pcaf ls) ms_a' ==> ?ms'. ((wm.weak ms ls ms') /\ (R_a ms' ms_a'))) ==>
  (!ms ms_a ms' ms_a'. R_a ms ms_a ==> R_a ms' ms_a' ==> post_a ms_a ms_a' ==> post ms ms') ==>

  (abstract_jgmt_rel
    wm_a
    (pcaf l)
    (IMAGE pcaf ls)
    (pre_a)
    (post_a)) ==>

  (abstract_jgmt_rel
    wm
    l
    ls
    (pre)
    (post))
``,
  REPEAT GEN_TAC >>

  REWRITE_TAC [abstract_jgmt_rel_def] >>
(*
  REPEAT STRIP_TAC >>
*)
  DISCH_TAC >>
  DISCH_TAC >>
  DISCH_TAC >>
  DISCH_TAC >>
  DISCH_TAC >>

  DISCH_TAC >>
(*
  POP_ASSUM (K ALL_TAC)
*)
  POP_ASSUM (fn thm =>
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x. B ==> ?y. A`` (ASSUME_TAC o Q.SPEC `ms`) >>
    FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC std_ss [] >>
    REPEAT (PAT_X_ASSUM ``!x y. A ==> B`` (IMP_RES_TAC)) >>
    PAT_X_ASSUM ``!x. A ==> B`` (ASSUME_TAC o Q.SPEC `ms_a`) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    REPEAT (PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPECL [`ms`, `ms_a`, `ms'`, `ls`])) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    ASSUME_TAC thm) >>

  rename1 `post_a ms_a ms_a'` >>

  POP_ASSUM (IMP_RES_TAC) >>
  METIS_TAC []
);



val backlift_bir_m0_mod_EXISTS_thm = store_thm(
   "backlift_bir_m0_mod_EXISTS_thm", ``
!ms.
  ((m0_mod_bmr (T,T)).bmr_extra ms) ==>
?bs. (
  (bmr_rel (m0_mod_bmr (T,T)) bs ms) /\
  (bs.bst_status = BST_Running)
)
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [] >>
  ASM_REWRITE_TAC [bir_lifting_machinesTheory.bmr_rel_def] >>

  Q.ABBREV_TAC `bs = 
      <|
        bst_pc       := bir_block_pc (BL_Address (Imm32 (ms.base.REG RName_PC)));
        bst_environ  := BEnv (

 ("PSR_C" =+ SOME (BVal_Imm (bool2b ms.base.PSR.C)))
(("PSR_N" =+ SOME (BVal_Imm (bool2b ms.base.PSR.N)))
(("PSR_V" =+ SOME (BVal_Imm (bool2b ms.base.PSR.V)))
(("PSR_Z" =+ SOME (BVal_Imm (bool2b ms.base.PSR.Z)))

(("R0" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_0))))
(("R1" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_1))))
(("R2" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_2))))
(("R3" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_3))))
(("R4" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_4))))
(("R5" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_5))))
(("R6" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_6))))
(("R7" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_7))))
(("R8" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_8))))
(("R9" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_9))))
(("R10" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_10))))
(("R11" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_11))))
(("R12" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_12))))
(("LR" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_LR))))
(("SP_main" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_main))))
(("SP_process" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_process))))
(("ModeHandler" =+ SOME (BVal_Imm (bool2b (ms.base.CurrentMode = Mode_Handler))))
(("countw" =+ SOME (BVal_Imm (Imm64 (ms.countw))))
(("MEM" =+ SOME (BVal_Mem Bit32 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.base.MEM))))

(("tmp_PSR_C" =+ SOME (BVal_Imm (Imm1 0w)))
(("tmp_PSR_N" =+ SOME (BVal_Imm (bool2b ms.base.PSR.N)))
(("tmp_PSR_V" =+ SOME (BVal_Imm (bool2b ms.base.PSR.V)))
(("tmp_PSR_Z" =+ SOME (BVal_Imm (bool2b ms.base.PSR.Z)))

(("tmp_R0" =+ SOME (BVal_Imm (Imm32 0w)))
(("tmp_R1" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_1))))
(("tmp_R2" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_2))))
(("tmp_R3" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_3))))
(("tmp_R4" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_4))))
(("tmp_R5" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_5))))
(("tmp_R6" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_6))))
(("tmp_R7" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_7))))
(("tmp_R8" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_8))))
(("tmp_R9" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_9))))
(("tmp_R10" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_10))))
(("tmp_R11" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_11))))
(("tmp_R12" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_12))))
(("tmp_LR" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_LR))))
(("tmp_SP_main" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_main))))
(("tmp_SP_process" =+ SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_process))))
(("tmp_ModeHandler" =+ SOME (BVal_Imm (bool2b (ms.base.CurrentMode = Mode_Handler))))
(("tmp_countw" =+ SOME (BVal_Imm (Imm64 (ms.countw))))
(("tmp_MEM" =+ SOME (BVal_Mem Bit32 Bit8 (bir_mmap_w_w2n (bir_mf2mm (K 0w)))))

(("tmp_PC" =+ SOME (BVal_Imm (Imm32 0w)))
(("tmp_COND" =+ SOME (BVal_Imm (Imm1 0w)))
  (K NONE)
)))))))))))))))))))))))
))))))))))))))))))))))))


);
        bst_status   := BST_Running
      |>` >>
  Q.EXISTS_TAC `bs` >>

  REPEAT STRIP_TAC >- (
    Q.UNABBREV_TAC `bs` >>
    EVAL_TAC
  ) >- (
    Q.UNABBREV_TAC `bs` >>
    EVAL_TAC >>
    SIMP_TAC std_ss [] >>
    REWRITE_TAC [GSYM bir_exp_liftingTheory.bir_mf2mm_def] >>
    REWRITE_TAC [GSYM bir_exp_liftingTheory.bir_mmap_w_w2n_def] >>
    REWRITE_TAC [GSYM bir_exp_memTheory.bir_load_mmap_def] >>

    REWRITE_TAC [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm, wordsTheory.n2w_w2n] >>
    MATCH_MP_TAC EQ_EXT >>
    SIMP_TAC std_ss []
  ) >- (
    Q.UNABBREV_TAC `bs` >>
    EVAL_TAC
  ) >>

  Q.UNABBREV_TAC `bs` >>
  EVAL_TAC
);


val backlift_bir_m0_mod_pc_rel_thm = store_thm(
   "backlift_bir_m0_mod_pc_rel_thm", ``
!p ms bs.
  (bs.bst_status = BST_Running) ==>
  (bmr_rel (m0_mod_bmr (T,T)) bs ms) ==>
  ((bir_etl_wm p).pc bs = (\l. BL_Address (Imm32 (l))) (m0_mod_weak_model.pc ms))
``,
  REPEAT STRIP_TAC >>
  `bir_machine_lifted_pc (m0_mod_bmr (T,T)).bmr_pc bs ms` by (
    FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_rel_def]
  ) >>
  POP_ASSUM (MP_TAC) >>
  POP_ASSUM (K ALL_TAC) >>

  EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  )
);


val backlift_bir_m0_mod_pre_abstr_def = Define `
    backlift_bir_m0_mod_pre_abstr pre pre_bir =
      !ms bs.
        (bmr_rel (m0_mod_bmr (T,T)) bs ms) ==>
        (pre ms) ==>
        (pre_bir bs)
`;

(* =============================================================================== *)
local
open HolKernel Parse boolLib bossLib;

open bir_immTheory;
open bir_programTheory;
open bir_wm_instTheory;
open bir_program_multistep_propsTheory;
open bir_auxiliaryTheory;

(* From lifter: *)
open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;

(* From comp: *)
open abstract_hoare_logicTheory;
open abstract_simp_hoare_logicTheory;

open HolBASimps;
open HolBACoreSimps;
open abstract_hoare_logicSimps;

open bir_auxiliaryLib;
in

(* TODO: copied and adjusted *)
val set_of_address_in_all_address_labels_thm = prove (
  ``!l adds.
    l IN (IMAGE BL_Address adds) ==>
    l IN {l | IS_BL_Address l}``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def, IMAGE_DEF]
);

(* TODO: copied and adjusted "bir_backlifterTheory.bir_exec_to_labels_TO_exec_to_addr_label_n" *)
val bir_exec_to_labels_TO_exec_to_addr_label_n_GEN =
  store_thm("bir_exec_to_labels_TO_exec_to_addr_label_n_GEN",
  ``!bs' ls p bs lo0 n n0.

    (* TODO: should remove this assumption *)
    (bs'.bst_pc.bpc_label IN (IMAGE BL_Address ls)) ==>

    (bir_exec_to_labels (IMAGE BL_Address ls) p bs = BER_Ended lo0 n n0 bs') ==>
    ?n' lo c_addr_labels.
         (n' > 0) /\
         (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n c_addr_labels bs')``,

REPEAT STRIP_TAC >>

(*
`bs'.bst_pc.bpc_label IN (IMAGE BL_Address ls)` by (
  cheat
) >>
*)

subgoal `bs'.bst_pc.bpc_label IN {l | IS_BL_Address l}` >- (
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
				      bir_exec_to_labels_n_def] >>
subgoal `bir_pc_cond_impl (F,
	   (\pc.
	     (pc.bpc_index = 0) /\
	     pc.bpc_label IN (IMAGE BL_Address ls))) (F, (\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))` >- (
  FULL_SIMP_TAC std_ss [bir_pc_cond_impl_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
IMP_RES_TAC bir_exec_steps_GEN_change_cond_Ended_SOME >>
Q.EXISTS_TAC `n2` >>
FULL_SIMP_TAC arith_ss [] >>
METIS_TAC []
);

val bir_exec_to_labels_TO_exec_to_addr_label_n_32 = store_thm(
   "bir_exec_to_labels_TO_exec_to_addr_label_n_32", ``
!bs' ls p bs lo0 n n0.
    (bir_exec_to_labels (IMAGE (\l. BL_Address (Imm32 l)) ls) p bs = BER_Ended lo0 n n0 bs') ==>
    (~(bir_state_is_terminated bs')) ==>
    (bs'.bst_pc.bpc_label IN (IMAGE (\l. BL_Address (Imm32 l)) ls)) ==>

    ?n' lo.
         (n' > 0) /\
         (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n n' bs')
``,
  REPEAT STRIP_TAC >>

  `IMAGE (\l. BL_Address (Imm32 l)) ls = IMAGE BL_Address (IMAGE Imm32 ls)` by (
    FULL_SIMP_TAC std_ss [EXTENSION, IN_IMAGE] >>
    METIS_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  IMP_RES_TAC bir_exec_to_labels_TO_exec_to_addr_label_n_GEN >>
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>

  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
);

val bir_exec_addr_label_n_NONZERO_labels = prove(
  ``!c_addr_labels ms' bs bs' mls (p:'a bir_program_t) n n' lo li.
    (* Execution from BIR HT *)
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n c_addr_labels bs') ==>
    ~bir_state_is_terminated bs' ==>
    (n' > 0) ==>
    c_addr_labels > 0``,

REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>


  Cases_on `c_addr_labels = 0` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
                          bir_exec_steps_GEN_SOME_EQ_Ended] >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC arith_ss []
);

val bir_m0_mod_exec_in_end_label_set = prove(
  ``!ms' bs' mls li.
    (bs'.bst_pc = bir_block_pc (BL_Address li)) ==>
    (bs'.bst_pc.bpc_label IN (IMAGE (\l. BL_Address (Imm32 l)) mls)) ==>

    (* BMR relation between the final states *)
    ~bir_state_is_terminated bs' ==>
    bmr_rel (m0_mod_bmr (T,T)) bs' ms' ==>

    ms'.base.REG RName_PC IN mls``,

REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>

  subgoal `bs'.bst_pc = bir_block_pc (BL_Address (Imm32 (ms'.base.REG RName_PC)))` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_is_terminated_def] >>
    POP_ASSUM MP_TAC >>
    EVAL_TAC >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def]
  ) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setLib.PRED_SET_ss)
    [bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

(* TODO: this is copied "bir_backlifterTheory.bir_arm8_inter_exec_notin_end_label_set" and adapted *)
val bir_inter_exec_notin_end_label_set_GEN = prove(
  ``!mls p bs l n0 n' n'' lo lo' c_st c_st' bs' bs''.
    (bir_exec_to_labels (IMAGE (\l. BL_Address l) mls) p bs = BER_Ended l c_st n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n'' = BER_Ended lo' c_st' n'' bs'') ==>
    c_st' < c_st ==>
    n'' > 0 ==>
    ~bir_state_is_terminated bs'' ==>
    bs''.bst_pc.bpc_label NOTIN (IMAGE (\l. BL_Address l) mls)``,

REPEAT STRIP_TAC >>
(* NOTE: The number of taken statement steps is c_st for both the to-label execution
 * and the to-addr-label-execution. *)
(* The number of PCs counted (= in mls) at c_st' statement steps must be 0. *)
subgoal `~bir_state_COUNT_PC (F,
	  (\pc.
	       (pc.bpc_index = 0) /\
	       pc.bpc_label IN (IMAGE (\l. BL_Address l) mls)))
	      (bir_exec_infinite_steps_fun p bs c_st')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended] >>
  (* Ergo, at c_st' statement steps, the PC label is not in mls, which follows after
   * some arithmetic. *)
  QSPECL_X_ASSUM ``!(n:num). (n < c_st) ==> _`` [`c_st'`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  subgoal `c_st' > 0` >- (
    METIS_TAC [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_SOME_EQ_Ended_Running_steps,
	       bir_state_is_terminated_def]
  ) >>
  FULL_SIMP_TAC std_ss [NUM_LSONE_EQZ, bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
  QSPECL_X_ASSUM ``!j. _`` [`PRE c_st'`] >>
  SUBGOAL_THEN ``SUC (PRE (c_st':num)) = c_st'`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  METIS_TAC [NUM_PRE_LT]
) >>
(* So either PC at c_st' statement steps has index 0, or it is not in mls.
 * But PC has index 0... *)
subgoal `bs''.bst_pc.bpc_index = 0` >- (
  METIS_TAC [bir_exec_to_addr_label_n_ended_running, bir_state_is_terminated_def]
) >>
(* ... which proves the goal, after some identification of states. *)
FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def, bir_exec_to_addr_label_n_def,
		      bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
);

val bir_inter_exec_notin_end_label_set_m0 = prove(
  ``!mls p bs l n0 n' n'' lo lo' c_st c_st' bs' bs''.
    (bir_exec_to_labels (IMAGE (\l. BL_Address (Imm32 l)) mls) p bs = BER_Ended l c_st n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n'' = BER_Ended lo' c_st' n'' bs'') ==>
    c_st' < c_st ==>
    n'' > 0 ==>
    ~bir_state_is_terminated bs'' ==>
    bs''.bst_pc.bpc_label NOTIN (IMAGE (\l. BL_Address (Imm32 l)) mls)``,

  REPEAT STRIP_TAC >>

  `IMAGE (\l. BL_Address (Imm32 l)) mls = IMAGE BL_Address (IMAGE Imm32 mls)` by (
    FULL_SIMP_TAC std_ss [EXTENSION, IN_IMAGE] >>
    METIS_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [bir_inter_exec_notin_end_label_set_GEN]
);

end;
(* ================================================================================= *)

val backlift_bir_m0_mod_SIM_thm = store_thm(
   "backlift_bir_m0_mod_SIM_thm", ``
!mu mms p mla ms bs bs' ls.
  (bir_is_lifted_prog (m0_mod_bmr (T,T)) mu mms p) ==>

  (MEM (BL_Address mla) (bir_labels_of_program p)) ==>
  (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
  (EVERY (bmr_ms_mem_contains (m0_mod_bmr (T,T)) ms) mms) ==>

  (~(bir_state_is_terminated bs)) ==>
  (~(bir_state_is_terminated bs')) ==>

  (bmr_rel (m0_mod_bmr (T,T)) bs ms) ==>
  ((bir_etl_wm p).weak bs (IMAGE (\l. BL_Address (Imm32 l)) ls) bs') ==>
  ?ms'. ((m0_mod_weak_model.weak ms ls ms') /\
         (bmr_rel (m0_mod_bmr (T,T)) bs' ms'))
``,
  REPEAT STRIP_TAC >>

  POP_ASSUM MP_TAC >>

  SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS) [bir_wm_instTheory.bir_etl_wm_def, m0_mod_weak_model_def, m_weak_model_def, m_weak_trs_def, bir_wm_instTheory.bir_weak_trs_EQ] >>
  REPEAT STRIP_TAC >>
(*
bir_weak_trs_EQ
  CASE_TAC >>
  CASE_TAC >>
  FULL_SIMP_TAC (std_ss) [] >>
*)

  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute_32_8_thm >>
  Q.ABBREV_TAC `stepf = (m0_mod_bmr (T,T)).bmr_step_fun` >>
(*
  REV_FULL_SIMP_TAC (std_ss) [] >>
*)

  IMP_RES_TAC bir_exec_to_labels_TO_exec_to_addr_label_n_32 >>
  PAT_X_ASSUM ``!x.A`` (fn thm => (IMP_RES_TAC thm >> ASSUME_TAC thm)) >>
  Q.EXISTS_TAC `ms'` >>
  ASM_REWRITE_TAC [] >>
  Q.EXISTS_TAC `n'` >>
  ASM_REWRITE_TAC [] >>

  CONJ_TAC >- (
    `bs'.bst_pc.bpc_label IN IMAGE (\l. BL_Address (Imm32 l)) ls` by (
      ASM_REWRITE_TAC []
    ) >>
    IMP_RES_TAC bir_m0_mod_exec_in_end_label_set
  ) >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `?lo2 n2 n2' bs''. bir_exec_to_addr_label_n p bs n'' = BER_Ended lo2 n2 n2' bs''` by (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
    METIS_TAC [bir_program_multistep_propsTheory.bir_exec_steps_GEN_decrease_max_steps_Ended_SOME]
  ) >>

  `~bir_state_is_terminated bs''` by (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
    METIS_TAC [bir_program_multistep_propsTheory.bir_exec_steps_GEN_decrease_max_steps_Ended_terminated]
  ) >>

  PAT_X_ASSUM ``!x.A`` IMP_RES_TAC >>

  `n2' = n''` by (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
    METIS_TAC [bir_program_multistep_propsTheory.bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `n2 < n` by (
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
	       bir_exec_to_labels_n_def,
	       bir_program_multistep_propsTheory.bir_exec_steps_GEN_decrease_max_steps_Ended_steps_taken]
  ) >>

  IMP_RES_TAC bir_inter_exec_notin_end_label_set_m0 >>

  `bs''.bst_pc.bpc_label = (\l. BL_Address (Imm32 l)) (ms''.base.REG RName_PC)` by (
    `(bir_etl_wm p).pc bs'' = (\l. BL_Address (Imm32 l)) (m0_mod_weak_model.pc ms'')` by (
      FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
      METIS_TAC [backlift_bir_m0_mod_pc_rel_thm]
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss++abstract_hoare_logicSimps.bir_wm_SS) [bir_block_pc_def, bir_wm_instTheory.bir_etl_wm_def, m0_mod_weak_model_def, m_weak_model_def, m_weak_trs_def, bir_wm_instTheory.bir_weak_trs_def]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
);


val backlift_bir_m0_mod_post_concr_def = Define `
    backlift_bir_m0_mod_post_concr post_bir post =
      !ms bs ms' bs'.
        (bmr_rel (m0_mod_bmr (T,T)) bs ms) ==>
        (bmr_rel (m0_mod_bmr (T,T)) bs' ms') ==>
        (post_bir bs bs') ==>
        (post ms ms')
`;



val backlift_bir_m0_mod_contract_thm = store_thm(
   "backlift_bir_m0_mod_contract_thm", ``
(*
!mla.
  bir_is_lifted_prog (m0_mod_bmr (T,T)) mu mms p ==>
  (MEM (BL_Address mla) (bir_labels_of_program bprog)) ==>
*)

!pre pre_bir post_bir post p l ls mms mu.
  (bir_is_lifted_prog (m0_mod_bmr (T,T)) mu mms p) ==>

  (!ms. pre ms ==>
    (EVERY (bmr_ms_mem_contains (m0_mod_bmr (T,T)) ms) mms)) ==>
  (!ms. pre ms ==> (m0_mod_bmr (T,T)).bmr_extra ms) ==>

  (!bs. pre_bir bs ==> (
    (~(bir_state_is_terminated bs)) /\
    (?mla.
      (bs.bst_pc = bir_block_pc (BL_Address mla)) /\
      (MEM (BL_Address mla) (bir_labels_of_program p))))) ==>

  (!bs bs'. post_bir bs bs' ==>
    (~(bir_state_is_terminated bs'))) ==>

  (backlift_bir_m0_mod_pre_abstr pre pre_bir) ==>
  (backlift_bir_m0_mod_post_concr post_bir post) ==>

  (abstract_jgmt_rel
    (bir_etl_wm p)
    (BL_Address (Imm32 l))
    (IMAGE (\x. (BL_Address (Imm32 x))) ls)
    (pre_bir)
    (post_bir)) ==>

  (abstract_jgmt_rel
    m0_mod_weak_model
    l
    ls
    (pre)
    (post))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_pre_abstr_def, backlift_bir_m0_mod_post_concr_def] >>

  IMP_RES_TAC
    (INST_TYPE
      [alpha  |-> Type`:bir_state_t`, beta |-> Type`:bir_label_t`, delta |-> Type`:word32`]
      backlift_contract_GEN_thm) >>

  POP_ASSUM (ASSUME_TAC o Q.SPECL [`\ms bs. bs.bst_status = BST_Running`, `(\ms. \bs. (bmr_rel (m0_mod_bmr (T,T)) bs ms))`]) >>
  FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_EXISTS_thm] >>

  POP_ASSUM (fn thm => ASSUME_TAC (MATCH_MP thm (SPEC ``p:'a bir_program_t`` backlift_bir_m0_mod_pc_rel_thm))) >>

  POP_ASSUM (IMP_RES_TAC) >>

(*
*)
  `!ms bs bs' ls.
     pre ms ==> pre_bir bs ==> post_bir bs bs' ==> bmr_rel (m0_mod_bmr (T,T)) bs ms ==>
     (bir_etl_wm p).weak bs (IMAGE (λl. BL_Address (Imm32 l)) ls) bs' ==>
     ?ms'. ((m0_mod_weak_model.weak ms ls ms') /\ (bmr_rel (m0_mod_bmr (T,T)) bs' ms'))` by (
    REPEAT STRIP_TAC >>
    IMP_RES_TAC backlift_bir_m0_mod_SIM_thm >>
    PAT_X_ASSUM ``!x. pre x ==> A /\ B`` (IMP_RES_TAC) >>
    FULL_SIMP_TAC std_ss [] >>
    PAT_X_ASSUM ``!x. A`` (IMP_RES_TAC) >>
    METIS_TAC []
  ) >>

  POP_ASSUM (fn thm2 => POP_ASSUM (fn thm => ASSUME_TAC (MATCH_MP thm thm2))) >>

(*
  POP_ASSUM (fn thm =>
      ASSUME_TAC
        (MATCH_MP
           thm
           (SPEC ``p:'a bir_program_t`` backlift_bir_m0_mod_SIM_thm))
    ) >>
*)

  POP_ASSUM (IMP_RES_TAC) >>
  FULL_SIMP_TAC std_ss []
);

(*
  `!ms.
       (m0_mod_bmr (T,T)).bmr_extra ms ==>
       ?bs.
         (\ms bs. bmr_rel (m0_mod_bmr (T,T)) bs ms) ms bs` by (
    METIS_TAC [backlift_bir_m0_mod_EXISTS_thm]
  ) >>
  ASSUME_TAC backlift_bir_m0_mod_EXISTS_thm >>

*)



(*
  POP_ASSUM (ASSUME_TAC o Q.SPECL [``, ``]) >>
  FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_pc_rel_thm] >>
*)





(*
  ASSUME_TAC
    (MATCH_MP
      (INST_TYPE
        [beta |-> Type`:bir_label_t`, delta |-> Type`:word32`]
        (SIMP_RULE std_ss []
          (MATCH_MP

)))
      ) >>
*)


val m0_mod_R_def = Define `
  m0_mod_R ms mms = (ms = m0_mod_inv mms)
`;

val m0_SIM_m0_mod_NONE_step_thm = store_thm(
   "m0_SIM_m0_mod_NONE_step_thm", ``
!ms mms.
  (m0_mod_R ms mms) ==>
  (NextStateM0 ms = NONE) ==>
  (NextStateM0_mod mms = NONE)
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.NextStateM0_mod_def]
);

val m0_mod_SIM_m0_NONE_step_thm = store_thm(
   "m0_mod_SIM_m0_NONE_step_thm", ``
!ms mms.
  (*
  (OPTION_ALL (\ms'. ms'.count < (2 ** 64)) (NextStateM0 (m0_mod_inv mms))) ==>
  *)
  (!ms'. NextStateM0 (m0_mod_inv mms) = SOME ms' ==> ms'.count < (2 ** 64)) ==>

  (m0_mod_R ms mms) ==>
  (NextStateM0_mod mms = NONE) ==>
  (NextStateM0 ms = NONE)
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.NextStateM0_mod_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `NextStateM0 (m0_mod_inv mms)` >> (
    FULL_SIMP_TAC std_ss [m0_mod_stepTheory.m0_mod_def]
  )
);

val m0_SIM_m0_mod_SOME_step_thm = store_thm(
   "m0_SIM_m0_mod_SOME_step_thm", ``
!ms mms ms'.
  (ms'.count < (2 ** 64)) ==>

  (m0_mod_R ms mms) ==>
  (NextStateM0 ms = SOME ms') ==>
  (?mms'.
    (NextStateM0_mod mms = SOME mms') /\
    (m0_mod_R ms' mms'))
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.NextStateM0_mod_def] >>

  SIMP_TAC std_ss [m0_mod_stepTheory.m0_mod_def] >>
  REPEAT STRIP_TAC >>

  SIMP_TAC std_ss [m0_mod_stepTheory.m0_mod_inv_def] >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_mod_state``))) [] >>

  `w2n ((n2w ms'.count):word64) = ms'.count` by (
    SIMP_TAC std_ss [wordsTheory.w2n_n2w] >>
    ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MOD, wordsTheory.dimword_64]
  ) >>
  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) [m0Theory.m0_state_component_equality]
);

val m0_mod_SIM_m0_SOME_step_thm = store_thm(
   "m0_mod_SIM_m0_SOME_step_thm", ``
!ms mms mms'.
  (m0_mod_R ms mms) ==>
  (NextStateM0_mod mms = SOME mms') ==>
  (?ms'.
    (NextStateM0 ms = SOME ms') /\
    (m0_mod_R ms' mms'))
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.NextStateM0_mod_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `NextStateM0 (m0_mod_inv mms)` >> (
    FULL_SIMP_TAC std_ss []
  ) >>

  PAT_X_ASSUM ``m0_mod x = A`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC std_ss [m0_mod_stepTheory.m0_mod_def] >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  ASM_SIMP_TAC std_ss [] >>

  SIMP_TAC std_ss [m0_mod_stepTheory.m0_mod_inv_def] >>
  SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_mod_state``))) [] >>

  `w2n ((n2w x.count):word64) = x.count` by (
    SIMP_TAC std_ss [wordsTheory.w2n_n2w] >>
    ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MOD, wordsTheory.dimword_64]
  ) >>
  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) [m0Theory.m0_state_component_equality]
);

val m0_mod_SIM_m0_thm = store_thm(
   "m0_mod_SIM_m0_thm", ``
!ms mms n mms'.
  (m0_mod_R ms mms) ==>
  (FUNPOW_OPT NextStateM0_mod n mms = SOME mms') ==>
  (?ms'.
    (FUNPOW_OPT NextStateM0 n ms = SOME ms') /\
    (m0_mod_R ms' mms'))
``,
  Induct_on `n` >- (
    FULL_SIMP_TAC std_ss [bir_auxiliaryTheory.FUNPOW_OPT_REWRS] >>
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [bir_auxiliaryTheory.FUNPOW_OPT_REWRS] >>
  REPEAT STRIP_TAC >>

  Cases_on `NextStateM0_mod mms` >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  rename1 `NextStateM0_mod mms = SOME mms''` >>

  IMP_RES_TAC m0_mod_SIM_m0_SOME_step_thm >>
  PAT_X_ASSUM ``!x y. A`` IMP_RES_TAC >>

  Q.EXISTS_TAC `ms''` >>
  ASM_SIMP_TAC std_ss []
);

val backlift_m0_mod_m0_EXISTS_thm = store_thm(
   "backlift_m0_mod_m0_EXISTS_thm", ``
!ms.
(ms.count < (2 ** 64)) ==>
?mms.
  m0_mod_R ms mms
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  `w2n ((n2w ms.count):word64) = ms.count` by (
    SIMP_TAC std_ss [wordsTheory.w2n_n2w] >>
    ASM_SIMP_TAC arith_ss [arithmeticTheory.LESS_MOD, wordsTheory.dimword_64]
  ) >>

  Q.EXISTS_TAC `
      <|
        base   := ms;
        countw := n2w ms.count
       |>
    ` >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_mod_state``))) [] >>
  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) [m0Theory.m0_state_component_equality]
);


val backlift_m0_mod_m0_pc_rel_thm = store_thm(
   "backlift_m0_mod_m0_pc_rel_thm", ``
!ms mms.
  (m0_mod_R ms mms) ==>
  (m0_mod_weak_model.pc mms = m0_weak_model.pc ms)
``,
  SIMP_TAC std_ss [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS) [m0_mod_weak_model_def, m0_weak_model_def, m_weak_model_def, m_weak_trs_def] >>
  SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
);

val backlift_m0_mod_m0_pc_rel_EVAL_thm = store_thm(
   "backlift_m0_mod_m0_pc_rel_EVAL_thm", ``
!ms mms.
  (m0_mod_R ms mms) ==>
  (mms.base.REG RName_PC = ms.REG RName_PC)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC backlift_m0_mod_m0_pc_rel_thm >>

  FULL_SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS) [m0_mod_weak_model_def, m0_weak_model_def, m_weak_model_def, m_weak_trs_def]
);

val backlift_m0_mod_m0_pre_abstr_def = Define `
    backlift_m0_mod_m0_pre_abstr pre pre_mod =
      !ms mms.
        (m0_mod_R ms mms) ==>
        (pre ms) ==>
        (pre_mod mms)
`;

val backlift_m0_mod_m0_SIM_thm = store_thm(
   "backlift_m0_mod_m0_SIM_thm", ``
!ms mms mms' ls.
  (m0_mod_R ms mms) ==>
  (m0_mod_weak_model.weak mms ls mms') ==>
  (?ms'. m0_weak_model.weak ms ls ms' /\ m0_mod_R ms' mms')
``,
  REPEAT STRIP_TAC >>

  POP_ASSUM MP_TAC >>

  SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS) [m0_mod_weak_model_def, m0_weak_model_def, m_weak_model_def, m_weak_trs_def] >>
  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>
  REPEAT STRIP_TAC >>

  IMP_RES_TAC m0_mod_SIM_m0_thm >>
  Q.EXISTS_TAC `ms'` >>
  ASM_REWRITE_TAC [] >>
  Q.EXISTS_TAC `n` >>
  ASM_REWRITE_TAC [] >>

  CONJ_TAC >- (
    METIS_TAC [backlift_m0_mod_m0_pc_rel_EVAL_thm]
  ) >>

  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `n'`) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>

  IMP_RES_TAC m0_mod_SIM_m0_thm >>
  METIS_TAC [backlift_m0_mod_m0_pc_rel_EVAL_thm]
);

val backlift_m0_mod_m0_post_concr_def = Define `
    backlift_m0_mod_m0_post_concr post_mod post =
      !ms mms ms' mms'.
        (m0_mod_R ms mms) ==>
        (m0_mod_R ms' mms') ==>
        (post_mod mms mms') ==>
        (post ms ms')
`;

val backlift_m0_mod_m0_contract_thm = store_thm(
   "backlift_m0_mod_m0_contract_thm", ``

!pre pre_mod post_mod post l ls.
  (!ms. pre ms ==> (\ms. ms.count < (2 ** 64)) ms) ==>

  (backlift_m0_mod_m0_pre_abstr pre pre_mod) ==>
  (backlift_m0_mod_m0_post_concr post_mod post) ==>

  (abstract_jgmt_rel
    m0_mod_weak_model
    l
    ls
    (pre_mod)
    (post_mod)) ==>

  (abstract_jgmt_rel
    m0_weak_model
    l
    ls
    (pre)
    (post))
``,
  REPEAT STRIP_TAC >>

  ASSUME_TAC
    (INST_TYPE
      [alpha  |-> Type`:m0_mod_state`, beta |-> Type`:word32`, gamma |-> Type`:m0_state`, delta |-> Type`:word32`]
      backlift_contract_GEN_thm) >>

  POP_ASSUM (ASSUME_TAC o Q.SPECL [`m0_mod_weak_model`, `m0_weak_model`]) >>
  POP_ASSUM IMP_RES_TAC >>
  POP_ASSUM (ASSUME_TAC o Q.SPECL [`(\ms mms. T)`, `m0_mod_R`]) >>
  FULL_SIMP_TAC std_ss [backlift_m0_mod_m0_EXISTS_thm] >>

  POP_ASSUM (ASSUME_TAC o Q.SPECL [`I`]) >>
  FULL_SIMP_TAC std_ss [backlift_m0_mod_m0_pc_rel_thm] >>

  FULL_SIMP_TAC std_ss [backlift_m0_mod_m0_pre_abstr_def] >>
  POP_ASSUM IMP_RES_TAC >>

  POP_ASSUM (ASSUME_TAC o Q.SPECL [`post_mod`]) >>
  FULL_SIMP_TAC std_ss [IMAGE_I] >>
  `!ms mms mms' ls.
           pre ms ==>
           pre_mod mms ==>
           post_mod mms mms' ==>
           m0_mod_R ms mms ==>
           m0_mod_weak_model.weak mms ls mms' ==>
           ?ms'. m0_weak_model.weak ms ls ms' /\ m0_mod_R ms' mms'` by (
    REPEAT STRIP_TAC >>
    METIS_TAC [backlift_m0_mod_m0_SIM_thm]
  ) >>
  PAT_X_ASSUM ``A ==> B`` IMP_RES_TAC >>
  POP_ASSUM (ASSUME_TAC o Q.SPECL [`post`]) >>
  FULL_SIMP_TAC std_ss [backlift_m0_mod_m0_post_concr_def] >>
  POP_ASSUM IMP_RES_TAC
);


val _ = export_theory();
