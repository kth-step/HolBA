open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;

open bir_auxiliaryLib;

open HolBACoreSimps;

val _ = new_theory "bin_hoare_logic_test_AV";

(*
(* Executing till a certain set of labels is useful as well. Since we might loop
   outside this set of labels, infinite runs are possible. *)
val bir_exec_to_labels_n_def = Define `
  bir_exec_to_labels_n ls p state n =
  bir_exec_steps_GEN (F, \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) p state (SOME n)`

val bir_exec_to_labels_def = Define `
  bir_exec_to_labels ls p state = bir_exec_to_labels_n ls p state 1`
*)

(*
Datatype `bin_model_t =
  <|(* A function to obtain a state option from a state via
     * execution (transition) *)
    trs : 'a -> 'a option;
    (* A function to determine whether a transition between two
     * states is OK, through using a set of labels for which
     * execution must halt if reached, meaning they cannot be
     * touched in any intermediate step *)
    weak : 'a -> ('b -> bool) -> 'a -> bool;
    (* A function to obtain the program counter from a state *)
    pc : 'a -> 'b
   |>`;

*)

(*
val weak_model_def = Define `
  weak_model m =
    !ms ls ms'.
      (m.weak ms ls ms') =
        ?n.
          ((n > 0) /\
           (FUNPOW_OPT m.trs n ms = SOME ms') /\
           ((m.pc ms') IN ls)
          ) /\
          !n'.
            (((n' < n) /\ (n' > 0)) ==>
            ?ms''.
              (FUNPOW_OPT m.trs n' ms = SOME ms'') /\
              (~((m.pc ms'') IN ls))
            )`;
*)

(* TODO: bir_exec_block_n should probably return a BER_Ended or a
 * BER_Looping... *)
(* Try bir_exec_to_addr_label - but could cause more problems *)
(*
val bir_trs_def = Define `
  bir_trs prog ms =
  SOME (
    SND (
      SND (
        SND (bir_exec_block_n prog ms 1)
      )
    )
  )`;
*)
val bir_trs_def = Define `
  bir_trs (prog:'a bir_program_t) ms =
  let
    (_, _, _, st) = bir_exec_block_n prog ms 1
  in
   if st.bst_status = BST_Running
   then SOME st
   else NONE
`;

(* TODO: Move elsewhere... *)
val bir_get_current_statement_EMPTY =
  store_thm("bir_get_current_statement_EMPTY",
  ``!pc.
      bir_get_current_statement (BirProgram []) pc = NONE``,

FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_get_current_statement_def,
               bir_get_program_block_info_by_label_def,
               listTheory.INDEX_FIND_def]
);

val bir_exec_block_n_EXISTS = store_thm("bir_exec_block_n_EXISTS",
  ``!prog ms.
      ?a b c d.
        bir_exec_block_n prog ms 1 = (a, b, c, d)``,

REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated ms` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_TERMINATED]
) >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_steps_GEN_1_EQ_Ended] >>
cheat
(* Proof sketch from here:
   Either the PC of state ms points to a block in prog, or it does
   not. If it does not, we are OK, since any execution will result
   in Failed, terminating and yielding an Ended result.

   If the PC of state ms points to some block in prog, then do
   induction the list of basic statements: For the empty list, the
   PC must point to the ending statement. Consider the cases: if the
   ending statement is Halt, we are OK. If the ending statement is
   a CJmp whose condition fails to evaluate, we are OK. If the
   ending statement jumps outside the program, we are OK, since
   this will cause JumpOutside, which is a terminating state. In
   the case of jumps inside the program, there exist two
   possibilities: either jumps to other blocks (OK) or jumps to the
   same block, which will not give a Looping result, but will make
   pc_cond trigger.

   For every basic statement in a non-empty list, we will either
   terminate (by violating Assertions or Assumptions), in which case
   we are OK, or we will proceed to executing the next basic
   statement, or the ending statement (in which case the proof is
   same as above).

*)
(* OLD:
Cases_on `prog` >>
Cases_on `l` >- (
  (* Case: Empty program *)
  (* TODO: Lemma about empty program? *)
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
  EXISTS_TAC ``1:num`` >>
  EXISTS_TAC ``0:num`` >>
  FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_1,
                        bir_exec_step_state_def,
                        bir_exec_step_def,
                        arithmeticTheory.FUNPOW] >>
  CONJ_TAC >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_COUNT_PC_def,
                   bir_get_current_statement_EMPTY,
                   bir_state_set_failed_def],
  ) >>
  CONJ_TAC >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_get_current_statement_EMPTY,
                   bir_state_set_failed_def]
  ) >>
  CONJ_TAC >- (
    REPEAT STRIP_TAC >>
    (* TODO: Lemma stating that n < 1 ==> n = 0 ??? *)
    Cases_on `n` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [arithmeticTheory.FUNPOW],

      FULL_SIMP_TAC arith_ss []
    ]
  ) >>
  FULL_SIMP_TAC arith_ss []
) >>
  (* Case: Program nonempty. *)
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
  Cases_on `h` >>
  Cases_on `l` >| [
    (* Case: Statement list empty *)
    EXISTS_TAC ``1:num`` >> (* First witness is 1 in both cases *)
    FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_1,
                          bir_exec_step_state_def,
                          bir_exec_step_def] >>
    Cases_on `bir_get_current_statement (BirProgram (bir_block_t b [] b0::t)) ms.bst_pc` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_set_failed_def,
                     bir_state_COUNT_PC_def] >>
      FULL_SIMP_TAC arith_ss [] >>
      REPEAT STRIP_TAC >>
      Cases_on `n` >| [
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		      [arithmeticTheory.FUNPOW],

	FULL_SIMP_TAC arith_ss []
      ],

      (* Case: Current statement is something *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_def]
      Induct_on `x`
    ]

    (* Case: Statement list non-empty. Needed to show that it is
     * OK with termination on every statement, but quantifiers must
     * be instantiated with this in mind... *)

      (* Case of non-termination would also require a case split on
       * the ending statement causing termination? *)
  ]
  (* Should be length of block h... *)
  EXISTS_TAC ``((LENGTH (l:'a bir_stmt_basic_t list)) + 1):num`` >> 
  EXISTS_TAC ``1:num`` >>
  cheat
*)
);

val _ = Datatype `bir_weak_state =
    BWS_Regular bir_label_t
  | BWS_Top
  | BWS_Bottom
`;

val bir_get_weak_state_def = Define `
  bir_get_weak_state bir_state =
    if bir_state.bst_status = BST_Running
    then BWS_Regular (bir_state.bst_pc.bpc_label)
    else if bir_state.bst_status = BST_AssumptionViolated
    then BWS_Top
    else BWS_Bottom
`;

val bir_get_label_from_weak_state_def = Define `
  bir_get_label_from_weak_state ws =
    case ws of
      BWS_Regular l => SOME l
    | BWS_Top => NONE
    | BWS_Bottom => NONE
`;

val bir_get_label_set_from_weak_state_set_no_top_def = Define `
  bir_get_label_set_from_weak_state_set_no_top wss =
    (IMAGE THE
      ((IMAGE bir_get_label_from_weak_state wss) DELETE NONE)
    )
`;

val bir_weak_trs_def = Define `
  bir_weak_trs wss prog ms =
    let 
      ls = bir_get_label_set_from_weak_state_set_no_top wss
    in
    case (bir_exec_to_labels ls prog ms) of
      BER_Ended _ _ _ bir_state =>
        if ((bir_get_weak_state bir_state) IN wss)
        then SOME bir_state
        else NONE
    | BER_Looping _ => NONE
`;

(* 1. Instantiate a new weak model *)
val bir_etl_wm_def =
  Define `bir_etl_wm (prog :'a bir_program_t) = <|
    trs  := bir_trs prog;
    weak := (\ms wss ms'.
	       (bir_weak_trs wss prog ms = SOME ms')
	    );
    pc   := (\ms. bir_get_weak_state ms)
  |>`;

val wm_type = mk_thy_type {Tyop="bin_model_t",
                           Thy="bin_hoare_logic",
                           Args=[``:bir_state_t``,
                                 ``:bir_label_t``]
                          };

val bir_wm_SS = rewrites (flatten (map type_rws [wm_type]));

(* TODO: Move elsewhere... *)
val bir_get_current_statement_NONE_stmt =
  store_thm("bir_get_current_statement_NONE_stmt",
  ``!prog pc.
      (bir_get_current_statement prog pc = NONE) ==>
      (bir_get_current_block prog pc = NONE)
    ``,

FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_get_current_block_def,
               bir_get_current_statement_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_get_program_block_info_by_label
            prog pc.bpc_label` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >>
Cases_on `0 = LENGTH r.bb_statements` >>
Cases_on `0 < LENGTH r.bb_statements` >> (
FULL_SIMP_TAC arith_ss []
)
);

(* 2. Prove that weak_model bir_etl_wm *)
val bir_model_is_weak = store_thm("bir_model_is_weak",
  ``!(prog: 'a bir_program_t).
      weak_model (bir_etl_wm prog)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [weak_model_def, bir_etl_wm_def] >>
FULL_SIMP_TAC std_ss [bir_weak_trs_def, LET_DEF] >>
REPEAT STRIP_TAC >>
CASE_TAC >| [
  (* Case 1: Result of bir_exec_to_labels is Ended *)
  CASE_TAC >| [
    (* Case 1A: Weak state counterpart of b is in ls *)
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
    EQ_TAC >| [
      (* Part one: Assuming b = ms', show bir_trs plays nice *)
      REPEAT DISCH_TAC >>
      (* subsume b... *)
      Q.PAT_X_ASSUM `b = ms'`
                    (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
                            bir_exec_steps_GEN_SOME_EQ_Ended] >>
      EXISTS_TAC ``m:num`` >>
      (* TODO: Make lemma... *)
      subgoal `!prog ms m l n c_l' ms'.
        (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
        ?m'.
        (FUNPOW_OPT (bir_trs prog) m' ms = SOME ms')` >- (
        cheat
      ) >>
      FULL_SIMP_TAC (arith_ss++holBACore_ss) [] >>
      REPEAT STRIP_TAC >>
      (* TODO: Use bir_exec_steps_GEN_SOME_EQ_Ended and possibly
       * bir_exec_block_n_TO_steps_GEN *)
      cheat,

      (* Part two: Assuming bir_trs plays nice, show that b = ms' *)
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
      cheat
    ],

    (* Case 1B: Weak state counterpart of b is NOT in ls *)
    FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
    cheat
  ],

  (* Case 2: Result of bir_exec_to_labels is Looping *)
  (* Show that weak state of ms' cannot be in ls *)
  FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
  cheat
]
);








(*


      Cases_on `n > 0` >| [
        (* Number of execution steps is non-zero (regular case) *)
        (* Also use the fact that final state is Running *)
        subgoal
          `FUNPOW_OPT (bir_trs prog) n ms =
             SOME (bir_exec_infinite_steps_fun prog ms n)` >- (
          cheat
        ) >>
        FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def] >>
        Cases_on `ms'.bst_status` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) []
        ) >| [
          (* Case: Final state is Running *)
          REPEAT STRIP_TAC >>
          FULL_SIMP_TAC std_ss [] >>
          QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
          REV_FULL_SIMP_TAC std_ss [] >>
          (* TODO: Some kind of kinduction proof on n'? *)
          (* bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0 *)
          cheat,

          (* Case: JumpOutside requires this additional
           *       simplification *)
          REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
        ],

	(* Number of execution steps is zero *)
	subgoal `n = 0` >- (
	  FULL_SIMP_TAC arith_ss []
	) >>
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		      [bir_exec_infinite_steps_fun_REWRS2,
		       bir_state_COUNT_PC_def] >>
	Cases_on `ms'.bst_status` >> (
	  FULL_SIMP_TAC (std_ss++holBACore_ss) []
	) >| [
	  (* Case: Final state is Running *)
	  FULL_SIMP_TAC std_ss
	    [bir_exec_infinite_steps_fun_COUNT_PCs_def],

	  (* Case: JumpOutside requires this additional
	   *       simplification *)
	  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
	]
      ],

      REPEAT STRIP_TAC >>
      QSPECL_X_ASSUM ``!n''. _`` [`n`] >>
      (* TODO: What to do here??? *)
      cheat
    ],

    (* Step 1B: Weak state of b is not in ls *)
    FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
    REPEAT STRIP_TAC >>
    (* You can choose between two disjuncts to prove. *)
    (* Disjunct 1: Need to prove that for all non-zero step numbers
     * n', repeated application of bir_trs resulting in SOME state
     * ms' (meaning, before termination) entails that ms' is not
     * in ls'.
     *
     * OK, since assumptions give that Ended was reached through
     * termination, meaning that ls' was not encountered before
     * terminating.
     * *)
    (* Disjunct 2: Need to prove that there exists a non-zero step
     * number n'' such that if repeated application of bir_trs n''
     * times gives SOME state ms'', then ms'' is in ls'.
     *
     * OK, since we can give a n'' larger than the steps leading to
     * termination, making the antecedent always false.
     * *)
    cheat
  ],

  (* Case 2: Result of bir_exec_to_labels is Looping *)
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
			bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_EQ_Looping] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
  (* Choice of two disjuncts... *)
(*
  DISJ1_TAC >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss
    [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
*)
  cheat
]
);
*)
(* These could be useful: *)
(* bir_exec_steps_GEN_SOME_EQ_Ended *)
(* bir_exec_steps_GEN_EQ_Ended *)
(* bir_exec_steps_GEN_change_cond_Ended_SOME *)
(* bir_exec_steps_GEN_1_EQ_Ended *)
(* bir_exec_to_labels_n_TO_bir_exec_block_n *)
(* bir_exec_block_n_TO_steps_GEN *)

val _ = export_theory();
