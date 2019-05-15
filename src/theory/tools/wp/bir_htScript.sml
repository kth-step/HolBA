open HolKernel Parse boolLib bossLib;

(* Theories from theory/bir: *)
open bir_programTheory bir_typing_progTheory bir_envTheory
     bir_auxiliaryTheory bir_valuesTheory bir_expTheory
     bir_exp_immTheory bir_typing_expTheory bir_immTheory;

(* Theories from theory/bir-support: *)
open bir_program_blocksTheory bir_program_terminationTheory
     bir_program_valid_stateTheory bir_exp_substitutionsTheory
     bir_bool_expTheory bir_program_env_orderTheory
     bir_program_multistep_propsTheory bir_exp_equivTheory
     bir_subprogramTheory;

(* Local theories: *)
open bir_wpTheory;

(* Simplification sets from theory/bir: *)
open HolBACoreSimps;

(* This theory contains theorems for manipulation of Hoare
 * triples not directly related to WP propagation. *)
val _ = new_theory "bir_ht";

val bir_stmtB_is_not_assume_def = Define `
  (bir_stmtB_is_not_assume (BStmt_Declare v) = T) /\
  (bir_stmtB_is_not_assume (BStmt_Assign v ex) = T) /\
  (bir_stmtB_is_not_assume (BStmt_Assert ex) = T) /\
  (bir_stmtB_is_not_assume (BStmt_Assume ex) = F) /\
  (bir_stmtB_is_not_assume (BStmt_Observe ec el obf) = T)
`;

val bir_stmtB_not_assume_never_assumviol =
  store_thm("bir_stmtB_not_assume_never_assumviol",
  ``!stmtb st obs st'.
    bir_stmtB_is_not_assume stmtb ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_stmtB stmtb st = (obs, st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)``,

REPEAT STRIP_TAC >>
Cases_on `st` >>
Cases_on `st'` >>
Cases_on `stmtb` >> (
  FULL_SIMP_TAC std_ss [bir_stmtB_is_not_assume_def,
                        bir_exec_stmtB_def]
) >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_stmt_declare_def] >>
  Cases_on `bir_env_varname_is_bound b0
              (bir_var_name b'')` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_set_failed_def,
                   bir_state_t_bst_status_fupd],

    Cases_on `bir_env_update (bir_var_name b'')
                (bir_declare_initial_value (bir_var_type b''))
                (bir_var_type b'')
                b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_set_failed_def,
		     bir_state_t_bst_status_fupd],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_set_failed_def,
		     bir_state_t_bst_status_fupd,
                     bir_state_t_bst_environ_fupd]
    ]
  ],

  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_stmt_assign_def, LET_DEF] >>
  Cases_on `bir_env_write b'' (bir_eval_exp b0'' b0) b0` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
		  [bir_state_set_failed_def,
		   bir_state_t_bst_status_fupd],

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_t_bst_environ_fupd]
  ],

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assert_def] >>
  Cases_on `bir_dest_bool_val (bir_eval_exp b'' b0)` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
		  [bir_state_set_failed_def,
		   bir_state_t_bst_status_fupd],

    Cases_on `x` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_set_failed_def,
		     bir_state_t_bst_status_fupd]
    )
  ],

  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_stmt_observe_def] >>
  Cases_on `bir_dest_bool_val (bir_eval_exp b'' b0)` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
		  [bir_state_set_failed_def,
		   bir_state_t_bst_status_fupd],

    Cases_on `x` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    )
  ]
]
);

val bir_stmtsB_has_no_assumes_def = Define `
  (bir_stmtsB_has_no_assumes [] = T) /\
  (bir_stmtsB_has_no_assumes (h::t) =
    (bir_stmtB_is_not_assume h) /\ (bir_stmtsB_has_no_assumes t)
  )
`;

(* TODO: Move this elsewhere... *)
val bir_exec_stmtB_exists =
  store_thm("bir_exec_stmtB_exists",
  ``!h st.
      ?obs' st'.
        bir_exec_stmtB h st = (obs', st')``,

Cases_on `h` >> (
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def]
) >>
FULL_SIMP_TAC std_ss [bir_exec_stmt_observe_def] >>
Cases_on `bir_dest_bool_val (bir_eval_exp b st.bst_environ)` >| [
  FULL_SIMP_TAC std_ss [],

  Cases_on `x` >> (
    FULL_SIMP_TAC std_ss []
  )
]
);

val bir_stmtsB_not_assume_never_assumviol =
  store_thm("bir_stmtsB_not_assume_never_assumviol",
  ``!stmtsB l c st l' c' st'.
    bir_stmtsB_has_no_assumes stmtsB ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_stmtsB stmtsB (l, c, st) = (l', c', st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)``,

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
                (SPECL [``(OPT_CONS obs_test l): 'a list``,
                        ``(SUC c):num``,
                        ``st_test:bir_state_t``,
                        ``l': 'a list``,
                        ``c':num``,
                        ``st':bir_state_t``] thm
                )
              ) >>
  REV_FULL_SIMP_TAC std_ss []
]
);

val bir_block_has_no_assumes_def = Define `
  bir_block_has_no_assumes block =
    bir_stmtsB_has_no_assumes block.bb_statements
`;

(* TODO: Move somewhere else... *)
val bir_exec_stmtE_not_assumviol =
  store_thm("bir_exec_stmtE_not_assumviol",
  ``!prog stmtE st.
      (st.bst_status <> BST_AssumptionViolated) ==>
      ((bir_exec_stmtE prog stmtE st).bst_status <>
         BST_AssumptionViolated)``,

REPEAT STRIP_TAC >>
Cases_on `stmtE` >| [
  (* Jmp *)
  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def,
                        bir_exec_stmt_jmp_def] >>
  Cases_on `bir_eval_label_exp b st.bst_environ` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_set_failed_def],

    Cases_on `x` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_failed_def,
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
  Cases_on `bir_dest_bool_val (bir_eval_exp b st.bst_environ)` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
  ) >>
  Cases_on `x` >> (
    FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def]
  ) >>> (TACS_TO_LT [
    Cases_on `bir_eval_label_exp b0 st.bst_environ` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_failed_def]
    ),

    Cases_on `bir_eval_label_exp b1 st.bst_environ` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_failed_def]
    )
  ]) >> (
    Cases_on `x` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_failed_def,
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
                                        bir_exec_stmt_halt_def]
]
);

(* TODO: Move this elsewhere... *)
val bir_exec_stmtsB_exists =
  store_thm("bir_exec_stmtsB_exists",
  ``!stmtsB l c st.
      ?l' c' st'.
        bir_exec_stmtsB stmtsB (l,c,st) = (l', c', st')``,

Induct_on `stmtsB` >- (
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def] >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC std_ss []
) >>
ASSUME_TAC (SPECL [``h:'a bir_stmt_basic_t``, ``st:bir_state_t``]
                  bir_exec_stmtB_exists) >>
FULL_SIMP_TAC std_ss [LET_DEF]
);

val bir_block_not_assume_never_assumviol =
  store_thm("bir_block_not_assume_never_assumviol",
  ``!prog bl st l' c' st'.
    bir_block_has_no_assumes bl ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_block prog bl st = (l', c', st')) ==>
    (st'.bst_status <> BST_AssumptionViolated)``,

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
		      ``l_test: 'a list``,
                      ``[]:'a list``,
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
                [bir_state_t_fn_updates, bir_state_t_bst_status,
                 bir_state_t_bst_pc],

  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_state_t_fn_updates, bir_state_t_bst_status,
                 bir_state_t_bst_pc] >>
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
);

val bir_prog_has_no_assumes_def = Define `
  (bir_prog_has_no_assumes (BirProgram []) = T) /\
  (bir_prog_has_no_assumes (BirProgram (h::t)) =
    (bir_block_has_no_assumes h) /\
    (bir_prog_has_no_assumes (BirProgram t))
  )
`;

(* TODO: Move this elsewhere... *)
val INDEX_FIND_PRE = store_thm("INDEX_FIND_PRE",
  ``!i j P l x.
    (0 < i) ==>
    (INDEX_FIND i       P l = SOME (j, x)) ==>
    (INDEX_FIND (PRE i) P l = SOME (PRE j, x))``,

Induct_on `l` >- (
  FULL_SIMP_TAC std_ss [listTheory.INDEX_FIND_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [listTheory.INDEX_FIND_def] >>
Cases_on `P h` >> (
  FULL_SIMP_TAC std_ss []
) >>
PAT_X_ASSUM ``!i j P x. _``
            (fn thm => ASSUME_TAC (SPEC ``(SUC i):num`` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``!j' P' x'. _`` (fn thm => IMP_RES_TAC thm) >>
REV_FULL_SIMP_TAC std_ss [arithmeticTheory.SUC_PRE]
);

val bir_prog_to_block_no_assumes = store_thm("bir_prog_to_block_no_assumes",
  ``!prog st bl.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    bir_block_has_no_assumes bl``,

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
    Cases_on `INDEX_FIND 1 (λx. x.bb_label = st.bst_pc.bpc_label)                   l` >> (
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
);

(* TODO: Move this elsewhere... *)
val bir_exec_block_exists =
  store_thm("bir_exec_block_exists",
  ``!prog bl st.
      ?l' c' st'.
        bir_exec_block prog bl st = (l', c', st')``,

Cases_on `prog` >>
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``bl.bb_statements:'a bir_stmt_basic_t list``,
                   ``[]: 'a list``, ``0:num``, ``st:bir_state_t``]
                  bir_exec_stmtsB_exists) >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `bir_state_is_terminated st'` >> (
  FULL_SIMP_TAC std_ss []
)
);

val bir_prog_not_assume_never_assumviol_exec_block_n =
  store_thm("bir_prog_not_assume_never_assumviol_exec_block_n",
  ``!prog st n bl ol nstep npc st'.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_block_n prog st n =
       (ol, nstep, npc, st')
    ) ==>
    (st'.bst_status <> BST_AssumptionViolated)``,

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
);
(* Formulated in terms of bir_exec_to_labels: *)
val bir_prog_not_assume_never_assumviol_exec_to_labels =
  store_thm("bir_prog_not_assume_never_assumviol_exec_to_labels",
  ``!ls prog st bl ol c_st c_l st'.
    (bir_get_current_block prog st.bst_pc = SOME bl) ==>
    bir_prog_has_no_assumes prog ==>
    (st.bst_status <> BST_AssumptionViolated) ==>
    (bir_exec_to_labels ls prog st =
       BER_Ended ol c_st c_l st'
    ) ==>
    (st'.bst_status <> BST_AssumptionViolated)``,

REPEAT STRIP_TAC >>
subgoal `bir_exec_to_labels_n ls prog st 1 =
           BER_Ended ol c_st c_l st'` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def]
) >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_block_n
);

val bir_exec_to_labels_triple_def = Define `
  bir_exec_to_labels_triple p l ls pre post =
  !s r.
    bir_env_vars_are_initialised s.bst_environ
                                 (bir_vars_of_program p) ==>
    ((s.bst_pc.bpc_index = 0) /\ (s.bst_pc.bpc_label = l)) ==>
    (s.bst_status = BST_Running) ==>
    bir_is_bool_exp_env s.bst_environ pre ==>
    (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
    ((bir_exec_to_labels ls p s) = r) ==>
    (?l1 c1 c2 s'.
      (r = BER_Ended l1 c1 c2 s') /\
      (s'.bst_status = BST_Running) /\
      bir_is_bool_exp_env s'.bst_environ post /\
      (bir_eval_exp post (s'.bst_environ) = bir_val_true) /\
      ((s'.bst_pc.bpc_index = 0) /\ (s'.bst_pc.bpc_label IN ls))
    )`;

(* TODO: Move to SubprogramTheory *)
val bir_state_is_failed_step_not_valid_pc =
  store_thm ("bir_state_is_failed_step_not_valid_pc",
``!p st.
  ~(bir_state_is_terminated st) ==>
  ~(bir_is_valid_pc p st.bst_pc) ==>
  ((bir_exec_step_state p st).bst_status = BST_Failed)``,

REPEAT STRIP_TAC >>
`~(IS_SOME (bir_get_current_statement p st.bst_pc))` by
  (METIS_TAC [bir_get_current_statement_IS_SOME]) >>
  FULL_SIMP_TAC std_ss [bir_exec_step_state_def,
                        bir_exec_step_def] >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss)
  [bir_state_set_failed_def]
);

val bir_never_assumviol_ht =
  store_thm("bir_never_assumviol_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_exec_to_labels_triple prog l ls pre post``,

REWRITE_TAC [bir_exec_to_labels_triple_def,
             bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s r. _``
            (fn thm => ASSUME_TAC
              (SPECL [``s:bir_state_t``,
                      ``r: 'a bir_execution_result_t``] thm)
            ) >>
Cases_on `r` >| [
  rename1 `bir_exec_to_labels ls prog s = BER_Ended l' n n0 s'` >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  subgoal `s.bst_status <> BST_AssumptionViolated` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] 
  ) >>
  Cases_on `bir_is_valid_pc prog s.bst_pc` >| [
    FULL_SIMP_TAC std_ss
                  [bir_is_valid_pc_def,
                   bir_get_program_block_info_by_label_def] >>
    subgoal `?bl. bir_get_current_block prog s.bst_pc = SOME bl`
      >- (
      FULL_SIMP_TAC std_ss [bir_get_current_block_def]
    ) >>
    IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_to_labels >>
    cheat,

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
    subgoal `~bir_state_is_terminated s` >- (
      FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
    ) >>
    IMP_RES_TAC bir_state_is_failed_step_not_valid_pc >>
    Cases_on `n` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_REWR_0],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_step_n_SUC, bir_exec_step_state_def] >>
      Cases_on `(bir_exec_step prog s)` >>
      ASSUME_TAC (el 4 (CONJUNCTS bir_exec_step_n_REWRS)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_is_terminated_def, LET_DEF] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ]
  ],

  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

val _ = export_theory();
