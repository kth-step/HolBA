open HolKernel Parse boolLib bossLib;

(* bir *)
open bir_programTheory;
open holba_auxiliaryTheory;
open HolBACoreSimps;

(* bir-support *)
open bir_program_blocksTheory;
open bir_program_multistep_propsTheory;

val _ = new_theory "bir_program_no_assume";

Definition bir_stmtB_is_not_assume_def:
  (bir_stmtB_is_not_assume (BStmt_Assume ex) = F) /\
  (bir_stmtB_is_not_assume _ = T)
End

Theorem bir_stmtB_not_assume_never_assumviol:
  !stmtb st obs st'.
    bir_stmtB_is_not_assume stmtb ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_stmtB stmtb st = (obs, st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)
Proof
REPEAT STRIP_TAC >>
  Cases_on `st` >>
  Cases_on `st'` >>
  Cases_on `stmtb` >> (
    FULL_SIMP_TAC std_ss [bir_stmtB_is_not_assume_def,
                          bir_exec_stmtB_def]
  ) >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_stmt_assign_def, LET_DEF] >>
    Cases_on `(bir_eval_exp b0'' b0)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def]
    ) >>
    Cases_on `bir_env_write b'' x b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [recordtype_bir_state_t_seldef_bst_environ_fupd_def]
    ],

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assert_def] >>
    Cases_on `(bir_eval_exp b'' b0)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def]
    ) >>
    Cases_on `bir_dest_bool_val x` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def],

      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_state_set_typeerror_def,
               recordtype_bir_state_t_seldef_bst_status_fupd_def]
      )
    ],

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_stmt_observe_def, LET_DEF] >>
    Cases_on `(bir_eval_exp b'' b0)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def]
    ) >>
    Cases_on `(bir_dest_bool_val x)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def]
    ) >>
    Cases_on `(x')` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_set_typeerror_def,
             recordtype_bir_state_t_seldef_bst_status_fupd_def] >>
      Cases_on `(EXISTS IS_NONE (MAP (λe. bir_eval_exp e b0) l))` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_state_set_typeerror_def,
               recordtype_bir_state_t_seldef_bst_status_fupd_def]
      )
    )
  ]
QED

Definition bir_stmtsB_has_no_assumes_def:
  (bir_stmtsB_has_no_assumes [] = T) /\
  (bir_stmtsB_has_no_assumes (h::t) =
    ((bir_stmtB_is_not_assume h) /\ (bir_stmtsB_has_no_assumes t))
  )
End

Theorem bir_stmtsB_not_assume_never_assumviol:
  !stmtsB l c st l' c' st'.
    bir_stmtsB_has_no_assumes stmtsB ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_stmtsB stmtsB (l, c, st) = (l', c', st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)
Proof
Induct_on `stmtsB` >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_stmtsB_has_no_assumes_def,
                   bir_exec_stmtsB_def]
  ) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_stmtsB_has_no_assumes_def,
                        bir_stmtB_is_not_assume_def,
                        bir_exec_stmtsB_def] >>
  Cases_on `bir_state_is_terminated st` >| [
    FULL_SIMP_TAC std_ss [],

    subgoal `?obs_test st_test.
               bir_exec_stmtB h st = (obs_test, st_test)` >- (
      FULL_SIMP_TAC std_ss [bir_exec_stmtB_exists]
    ) >>
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    IMP_RES_TAC bir_stmtB_not_assume_never_assumviol >>
    PAT_X_ASSUM ``!l'' c'' st''. _``
                (fn thm => ASSUME_TAC
                  (SPECL [``(OPT_CONS obs_test l): (num # 'a) list``,
                          ``(SUC c):num``,
                          ``st_test:bir_state_t``,
                          ``l': (num # 'a) list``,
                          ``c':num``,
                          ``st':bir_state_t``] thm
                  )
                ) >>
    REV_FULL_SIMP_TAC std_ss []
  ]
QED

Definition bir_block_has_no_assumes_def:
  bir_block_has_no_assumes block =
    bir_stmtsB_has_no_assumes block.bb_statements
End

Theorem bir_exec_stmtE_not_assumviol:
  !prog stmtE st.
      (st.bst_status <> BST_AssumptionViolated) ==>
      ((bir_exec_stmtE prog stmtE st).bst_status <>
         BST_AssumptionViolated)
Proof
REPEAT STRIP_TAC >>
  Cases_on `stmtE` >| [
    (* Jmp *)
    FULL_SIMP_TAC std_ss [bir_exec_stmtE_def,
                          bir_exec_stmt_jmp_def] >>
    Cases_on `bir_eval_label_exp b st.bst_environ` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_typeerror_def],

      Cases_on `x` >| [
        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_state_set_typeerror_def,
                       bir_exec_stmt_jmp_to_label_def] >>
        Cases_on `MEM (BL_Label s) (bir_labels_of_program prog)` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) []
        ),

        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_exec_stmt_jmp_to_label_def] >>
        Cases_on `MEM (BL_Address b')
                      (bir_labels_of_program prog)` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) []
        )
      ]
    ],

    (* CJmp *)
    FULL_SIMP_TAC std_ss [bir_exec_stmtE_def,
                          bir_exec_stmt_cjmp_def] >>
    Cases_on `(bir_eval_exp b st.bst_environ)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF]
    ) >>
    Cases_on `bir_dest_bool_val x` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
    ) >>
    Cases_on `x'` >> (
      FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def]
    ) >>> (TACS_TO_LT [
      Cases_on `bir_eval_label_exp b0 st.bst_environ` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_state_set_typeerror_def]
      ),

      Cases_on `bir_eval_label_exp b1 st.bst_environ` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_state_set_typeerror_def]
      )
    ]) >> (
      Cases_on `x'` >| [
        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_state_set_typeerror_def,
                       bir_exec_stmt_jmp_to_label_def] >>
        Cases_on `MEM (BL_Label s) (bir_labels_of_program prog)` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) []
        ),

        FULL_SIMP_TAC (std_ss++holBACore_ss)
                      [bir_exec_stmt_jmp_to_label_def] >>
        Cases_on `MEM (BL_Address b')
                      (bir_labels_of_program prog)` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) []
        )
      ]
    ),

    (* Halt *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def,
                                          bir_exec_stmt_halt_def] >>
    Cases_on `(bir_eval_exp b st.bst_environ)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def, LET_DEF]
    )
  ]
QED

Theorem bir_block_not_assume_never_assumviol:
  !prog bl st l' c' st'.
    bir_block_has_no_assumes bl ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_block prog bl st = (l', c', st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)
Proof
FULL_SIMP_TAC std_ss [bir_block_has_no_assumes_def,
                        bir_exec_block_def] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_stmtsB_not_assume_never_assumviol >>
  subgoal `?l_test c_test st'_test.
         bir_exec_stmtsB bl.bb_statements ([],0,st) =
               (l_test, c_test, st'_test)` >- (
    FULL_SIMP_TAC std_ss [bir_exec_stmtsB_exists]
  ) >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  PAT_X_ASSUM ``!st' l' l c' c. _``
          (fn thm => ASSUME_TAC
            (SPECL [``st'_test:bir_state_t``,
                ``l_test: (num # 'a) list``,
                        ``[]: (num # 'a) list``,
                ``c_test:num``,
                ``0:num``] thm
            )
          ) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Cases_on `bir_state_is_terminated st'_test` >| [
    Cases_on `st'_test` >>
    Cases_on `st` >>
    Cases_on `st'` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_t_fn_updates, recordtype_bir_state_t_seldef_bst_status_def,
                   recordtype_bir_state_t_seldef_bst_pc_def],

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_t_fn_updates, recordtype_bir_state_t_seldef_bst_status_def,
                   recordtype_bir_state_t_seldef_bst_pc_def] >>
    Cases_on `bir_state_is_terminated
                (bir_exec_stmtE prog bl.bb_last_statement
                   st'_test)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      Cases_on `st'` >>
      ASSUME_TAC (SPECL [``prog:'a bir_program_t``,
                         ``bl.bb_last_statement:bir_stmt_end_t``,
                         ``st'_test:bir_state_t``]
                        bir_exec_stmtE_not_assumviol
                 ) >>
      Q.ABBREV_TAC `st' = bir_exec_stmtE prog bl.bb_last_statement
                                         st'_test` >>
      Cases_on `st'` >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                        [bir_state_t_fn_updates]
    )
  ]
QED

Definition bir_prog_has_no_assumes_def:
  (bir_prog_has_no_assumes (BirProgram []) = T) /\
  (bir_prog_has_no_assumes (BirProgram (h::t)) =
    ((bir_block_has_no_assumes h) /\
    (bir_prog_has_no_assumes (BirProgram t)))
  )
End

Theorem bir_prog_to_block_no_assumes:
  !prog st bl.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    bir_block_has_no_assumes bl
Proof
Cases_on `prog` >>
  Induct_on `l` >| [
    FULL_SIMP_TAC std_ss [bir_get_current_block_def,
                          bir_get_program_block_info_by_label_def,
                          listTheory.INDEX_FIND_def],

    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_prog_has_no_assumes_def,
              bir_get_current_block_def,
              bir_get_program_block_info_by_label_def,
              listTheory.INDEX_FIND_def] >>
    Cases_on `h.bb_label = st.bst_pc.bpc_label` >| [
      FULL_SIMP_TAC std_ss [] >>
      RW_TAC std_ss [pairTheory.SND],

      FULL_SIMP_TAC std_ss [] >>
      Cases_on `INDEX_FIND 1 (\x. x.bb_label = st.bst_pc.bpc_label)                   l` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      Cases_on `x` >>
      REV_FULL_SIMP_TAC std_ss [] >>
      ASSUME_TAC (SPECL [``1:num``, ``q:num``,
                 ``(\x. x.bb_label = st.bst_pc.bpc_label):('a bir_block_t) -> bool``,
                 ``l:'a bir_block_t list``,
                 ``bl:'a bir_block_t``]
                (INST_TYPE [``:'a`` |-> ``:'a bir_block_t``]
                   INDEX_FIND_PRE
                )
             ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      PAT_X_ASSUM ``!st' bl'. _``
          (fn thm => ASSUME_TAC
            (SPECL [``st:bir_state_t``,
                ``bl:'a bir_block_t``] thm)
          ) >>
      FULL_SIMP_TAC std_ss []
    ]
  ]
QED

Theorem bir_prog_not_assume_never_assumviol_exec_block_n:
  !prog st n bl ol nstep npc st'.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_block_n prog st n = (ol, nstep, npc, st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)
Proof
Induct_on `n` >| [
    FULL_SIMP_TAC std_ss [bir_exec_block_n_def,
                          bir_exec_steps_GEN_REWR_no_steps,
                          valOf_BER_Ended_def],

    REPEAT STRIP_TAC >>
    ASSUME_TAC (SPECL [``prog:'a bir_program_t``,
               ``bl:'a bir_block_t``,
               ``st:bir_state_t``] bir_exec_block_exists) >>
    FULL_SIMP_TAC std_ss [] >>
    (* How to best swap variable names? *)
    rename1 `st'''.bst_status = BST_AssumptionViolated` >>
    rename1 `bir_exec_block prog bl st = (l',c',st')` >>
    rename1 `st''.bst_status = BST_AssumptionViolated` >>
    PAT_X_ASSUM ``!prog st bl ol nstep npc st'. _``
            (fn thm => ASSUME_TAC (SPECL [``prog: 'a bir_program_t``,
                                          ``st':bir_state_t``] thm)
            ) >>
    IMP_RES_TAC bir_prog_to_block_no_assumes >>
    IMP_RES_TAC bir_block_not_assume_never_assumviol >>
    IMP_RES_TAC bir_exec_block_n_block >>
    PAT_X_ASSUM ``!n. _``
            (fn thm => ASSUME_TAC
              (SPECL [``n:num``] thm)
            ) >>
    REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
    Cases_on `0 < c' /\
              bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0)) st'`
      >> (
        FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC std_ss []
     ) >> (
      Cases_on `~bir_state_is_terminated st'` >| [
        IMP_RES_TAC bir_exec_block_new_block_pc >>
        FULL_SIMP_TAC std_ss [optionTheory.IS_SOME_EXISTS] >>
        FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
        PAT_X_ASSUM ``(ol,nstep,npc,st'') = _``
            (fn thm => ASSUME_TAC
          (GSYM thm)
            ) >>
        (* TODO: The below finish is ugly... *)
        Cases_on `(bir_exec_block_n prog st' n)` >>
        Cases_on `r` >>
        Cases_on `r'` >>
        FULL_SIMP_TAC (std_ss++holBACore_ss) [],

        FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
        IMP_RES_TAC bir_exec_block_n_REWR_TERMINATED >>
        PAT_X_ASSUM ``!p n. _``
            (fn thm => ASSUME_TAC
          (SPECL [``prog:'a bir_program_t``, ``n:num``] thm)
            ) >>
        FULL_SIMP_TAC (std_ss++holBACore_ss) []
      ]
    )
  ]
QED

Theorem bir_prog_not_assume_never_assumviol_exec_to_labels:
  !ls prog st bl ol c_st c_l st'.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_to_labels ls prog st =
       BER_Ended ol c_st c_l st'
    ) ==>
    (st'.bst_status <> BST_AssumptionViolated)
Proof
REPEAT STRIP_TAC >>
  subgoal `bir_exec_to_labels_n ls prog st 1 =
             BER_Ended ol c_st c_l st'` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def]
  ) >>
  IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
  IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_block_n
QED

val _ = export_theory();
